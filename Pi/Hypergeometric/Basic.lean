/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.RCLike.Basic

/-!
# The generalized hypergeometric function `₃F₂`

We define `hypergeometric₃F₂`, the generalized hypergeometric function with three
numerator parameters and two denominator parameters, in a topological algebra `𝔸`
over a field `𝕂`:
$$
{}_3\mathrm{F}_2(a\ b\ c;\ d\ e;\ x)
  = \sum_{n=0}^{\infty} \frac{(a)_n (b)_n (c)_n}{(d)_n (e)_n} \frac{x^n}{n!},
$$
where `(a)ₙ` is the ascending Pochhammer symbol (see `ascPochhammer`).

This mirrors `ordinaryHypergeometric` (`₂F₁`) and is built on the same
`FormalMultilinearSeries.ofScalars` scaffold.

## Main definitions

* `hypergeometric₃F₂Series`: the `FormalMultilinearSeries` whose sum is `₃F₂`.
* `hypergeometric₃F₂`: the function, denoted `₃F₂`.
-/

@[expose] public section

open Nat FormalMultilinearSeries

section Field

variable {𝕂 : Type*} (𝔸 : Type*) [Field 𝕂] [Ring 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸]
  [IsTopologicalRing 𝔸]

/-- The coefficients in the `₃F₂` hypergeometric sum. -/
noncomputable def hypergeometric₃F₂Coefficient (a b c d e : 𝕂) (n : ℕ) : 𝕂 :=
  (n !⁻¹ : 𝕂) * (ascPochhammer 𝕂 n).eval a * (ascPochhammer 𝕂 n).eval b *
    (ascPochhammer 𝕂 n).eval c * ((ascPochhammer 𝕂 n).eval d)⁻¹ * ((ascPochhammer 𝕂 n).eval e)⁻¹

/-- `hypergeometric₃F₂Series 𝔸 (a b c d e : 𝕂)` is a `FormalMultilinearSeries`.
Its sum is the `hypergeometric₃F₂` map. -/
noncomputable def hypergeometric₃F₂Series (a b c d e : 𝕂) : FormalMultilinearSeries 𝕂 𝔸 𝔸 :=
  ofScalars 𝔸 (hypergeometric₃F₂Coefficient a b c d e)

variable {𝔸} (a b c d e : 𝕂)

/-- `hypergeometric₃F₂ (a b c d e : 𝕂) : 𝔸 → 𝔸`, denoted `₃F₂`, is the generalized hypergeometric
map, defined as the sum of `hypergeometric₃F₂Series 𝔸 a b c d e`.

Note that this takes the junk value `0` outside the radius of convergence. -/
noncomputable def hypergeometric₃F₂ (x : 𝔸) : 𝔸 :=
  (hypergeometric₃F₂Series 𝔸 a b c d e).sum x

@[inherit_doc]
notation "₃F₂" => hypergeometric₃F₂

theorem hypergeometric₃F₂Series_apply_eq (x : 𝔸) (n : ℕ) :
    (hypergeometric₃F₂Series 𝔸 a b c d e n fun _ => x) =
      hypergeometric₃F₂Coefficient a b c d e n • x ^ n := by
  rw [hypergeometric₃F₂Series, ofScalars_apply_eq]

theorem hypergeometric₃F₂_sum_eq (x : 𝔸) : (hypergeometric₃F₂Series 𝔸 a b c d e).sum x =
    ∑' n : ℕ, hypergeometric₃F₂Coefficient a b c d e n • x ^ n :=
  tsum_congr fun n => hypergeometric₃F₂Series_apply_eq a b c d e x n

theorem hypergeometric₃F₂_eq_tsum :
    ₃F₂ a b c d e = fun x : 𝔸 => ∑' n : ℕ, hypergeometric₃F₂Coefficient a b c d e n • x ^ n :=
  funext (hypergeometric₃F₂_sum_eq a b c d e)

theorem hypergeometric₃F₂Series_apply_zero (n : ℕ) :
    hypergeometric₃F₂Series 𝔸 a b c d e n (fun _ => 0) = Pi.single (M := fun _ => 𝔸) 0 1 n := by
  rw [hypergeometric₃F₂Series, ofScalars_apply_eq, hypergeometric₃F₂Coefficient]
  cases n <;> simp

@[simp]
theorem hypergeometric₃F₂_zero : ₃F₂ a b c d e (0 : 𝔸) = 1 := by
  rw [hypergeometric₃F₂, hypergeometric₃F₂_sum_eq,
    tsum_eq_single 0 fun n hn ↦ by simp [zero_pow hn], pow_zero]
  unfold hypergeometric₃F₂Coefficient
  simp

/-- If any parameter of the series is a sufficiently large nonpositive integer, then the series
term is zero. -/
lemma hypergeometric₃F₂Series_eq_zero_of_neg_nat {n k : ℕ}
    (h : k = -a ∨ k = -b ∨ k = -c ∨ k = -d ∨ k = -e) (hk : k < n) :
    hypergeometric₃F₂Series 𝔸 a b c d e n = 0 := by
  rw [hypergeometric₃F₂Series, ofScalars]
  rcases h with h | h | h | h | h
  all_goals
    ext
    simp [hypergeometric₃F₂Coefficient, (ascPochhammer_eval_eq_zero_iff n _).2 ⟨k, hk, h⟩]

end Field

section RCLike

open Asymptotics Filter Real Set Nat

open scoped Topology

variable {𝕂 : Type*} (𝔸 : Type*) [RCLike 𝕂] [NormedDivisionRing 𝔸] [NormedAlgebra 𝕂 𝔸]
  (a b c d e : 𝕂)

lemma hypergeometric₃F₂Series_eq_zero_iff (n : ℕ) :
    hypergeometric₃F₂Series 𝔸 a b c d e n = 0 ↔
      ∃ k < n, k = -a ∨ k = -b ∨ k = -c ∨ k = -d ∨ k = -e := by
  refine ⟨fun h ↦ ?_, fun ⟨_, h, hn⟩ ↦ hypergeometric₃F₂Series_eq_zero_of_neg_nat a b c d e hn h⟩
  rw [hypergeometric₃F₂Series, ofScalars_eq_zero] at h
  simp only [hypergeometric₃F₂Coefficient, _root_.mul_eq_zero, inv_eq_zero, or_assoc] at h
  rcases h with hn | h | h | h | h | h
  · simp [Nat.factorial_ne_zero] at hn
  all_goals
    have ⟨kn, hkn, hn⟩ := (ascPochhammer_eval_eq_zero_iff _ _).1 h
    exact ⟨kn, hkn, by tauto⟩

theorem hypergeometric₃F₂Series_norm_div_succ_norm (n : ℕ)
    (h : ∀ kn < n, (↑kn ≠ -a ∧ ↑kn ≠ -b ∧ ↑kn ≠ -c ∧ ↑kn ≠ -d ∧ ↑kn ≠ -e)) :
    ‖hypergeometric₃F₂Coefficient a b c d e n‖ /
        ‖hypergeometric₃F₂Coefficient a b c d e n.succ‖ =
      ‖a + n‖⁻¹ * ‖b + n‖⁻¹ * ‖c + n‖⁻¹ * ‖d + n‖ * ‖e + n‖ * ‖1 + (n : 𝕂)‖ := by
  have ne (x : 𝕂) (hx : ∀ kn < n, (kn : 𝕂) ≠ -x) :
      Polynomial.eval x (ascPochhammer 𝕂 n) ≠ 0 := fun H ↦
    have ⟨kn, hkn, he⟩ := (ascPochhammer_eval_eq_zero_iff n x).1 H
    hx kn hkn he
  have hstep : hypergeometric₃F₂Coefficient a b c d e n.succ =
      hypergeometric₃F₂Coefficient a b c d e n *
        ((a + n) * (b + n) * (c + n) * (d + n)⁻¹ * (e + n)⁻¹ * (1 + (n : 𝕂))⁻¹) := by
    simp only [hypergeometric₃F₂Coefficient, factorial_succ, cast_mul, cast_add, cast_one,
      ascPochhammer_succ_eval, mul_inv_rev]
    ring
  have hne : hypergeometric₃F₂Coefficient a b c d e n ≠ 0 := by
    unfold hypergeometric₃F₂Coefficient
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (inv_ne_zero (cast_ne_zero.2 (factorial_ne_zero n)))
      (ne a fun kn hkn ↦ (h kn hkn).1))
      (ne b fun kn hkn ↦ (h kn hkn).2.1))
      (ne c fun kn hkn ↦ (h kn hkn).2.2.1))
      (inv_ne_zero (ne d fun kn hkn ↦ (h kn hkn).2.2.2.1)))
      (inv_ne_zero (ne e fun kn hkn ↦ (h kn hkn).2.2.2.2))
  rw [hstep, norm_mul, div_mul_eq_div_div, div_self (norm_ne_zero_iff.2 hne), one_div]
  simp only [norm_mul, norm_inv, mul_inv_rev, inv_inv]
  ring

/-- The radius of convergence of `hypergeometric₃F₂Series` is unity if none of the parameters
are nonpositive integers. -/
theorem hypergeometric₃F₂Series_radius_eq_one
    (h : ∀ kn : ℕ, ↑kn ≠ -a ∧ ↑kn ≠ -b ∧ ↑kn ≠ -c ∧ ↑kn ≠ -d ∧ ↑kn ≠ -e) :
    (hypergeometric₃F₂Series 𝔸 a b c d e).radius = 1 := by
  have t (x y : 𝕂) : Tendsto (fun k : ℕ ↦ (x + k) / (y + k)) atTop (𝓝 1) := by
    convert! tendsto_add_mul_div_add_mul_atTop_nhds x y (1 : 𝕂) one_ne_zero <;> simp
  convert! ofScalars_radius_eq_of_tendsto 𝔸 _ one_ne_zero ?_
  suffices Tendsto
      (fun k : ℕ ↦ (a + k)⁻¹ * (b + k)⁻¹ * (c + k)⁻¹ * (d + k) * (e + k) * ((1 : 𝕂) + k))
      atTop (𝓝 1) by
    simp_rw [hypergeometric₃F₂Series_norm_div_succ_norm a b c d e _ (fun n _ ↦ h n)]
    simp only [← norm_inv, ← norm_mul, NNReal.coe_one]
    convert! Filter.Tendsto.norm this
    exact norm_one.symm
  have key (k : ℕ) :
      (a + k)⁻¹ * (b + k)⁻¹ * (c + k)⁻¹ * (d + k) * (e + k) * ((1 : 𝕂) + k) =
        (d + k) / (a + k) * ((e + k) / (b + k)) * ((1 + k) / (c + k)) := by ring
  simp_rw [key]
  simpa using ((t d a).mul (t e b)).mul (t 1 c)

end RCLike
