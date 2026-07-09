/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Pi.Hypergeometric.Basic
public import Mathlib.Analysis.Analytic.Basic

/-!
# The hypergeometric differential equation for `₃F₂`

The coefficients of `₃F₂` satisfy the recurrence
`(d + n)(e + n)(n + 1)·cₙ₊₁ = (a + n)(b + n)(c + n)·cₙ`, and on the ball of radius
one the function is represented by its power series, so it may be differentiated
term by term.
-/

set_option profiler true
set_option profiler.threshold 50

@[expose] public section

open Nat FormalMultilinearSeries

section Field

variable {𝕂 : Type*} [Field 𝕂] [CharZero 𝕂] (a b c d e : 𝕂)

theorem hypergeometric₃F₂Coefficient_succ (n : ℕ) (hd : d + n ≠ 0) (he : e + n ≠ 0) :
    (d + n) * (e + n) * (n + 1) * hypergeometric₃F₂Coefficient a b c d e (n + 1) =
      (a + n) * (b + n) * (c + n) * hypergeometric₃F₂Coefficient a b c d e n := by
  have hstep : hypergeometric₃F₂Coefficient a b c d e (n + 1) =
      ((n : 𝕂) + 1)⁻¹ * (d + n)⁻¹ * (e + n)⁻¹ * ((a + n) * (b + n) * (c + n)) *
        hypergeometric₃F₂Coefficient a b c d e n := by
    simp only [hypergeometric₃F₂Coefficient, factorial_succ, cast_mul, cast_add, cast_one,
      ascPochhammer_succ_eval, mul_inv_rev]
    ring
  rw [hstep]
  field_simp

end Field

section RCLike

open Filter

variable {𝕂 : Type*} (𝔸 : Type*) [RCLike 𝕂] [NormedDivisionRing 𝔸] [NormedAlgebra 𝕂 𝔸]
  [CompleteSpace 𝔸] (a b c d e : 𝕂)

/-- On the open ball of radius one, `₃F₂` is represented by its power series. -/
theorem hypergeometric₃F₂_hasFPowerSeriesOnBall
    (h : ∀ kn : ℕ, ↑kn ≠ -a ∧ ↑kn ≠ -b ∧ ↑kn ≠ -c ∧ ↑kn ≠ -d ∧ ↑kn ≠ -e) :
    HasFPowerSeriesOnBall (₃F₂ a b c d e) (hypergeometric₃F₂Series 𝔸 a b c d e) 0 1 := by
  have hr := hypergeometric₃F₂Series_radius_eq_one 𝔸 a b c d e h
  have := (hypergeometric₃F₂Series 𝔸 a b c d e).hasFPowerSeriesOnBall (by rw [hr]; exact one_pos)
  rwa [hr] at this

/-- For `‖z‖ < 1`, the defining series of `₃F₂` sums to its value. -/
theorem hypergeometric₃F₂_hasSum
    (h : ∀ kn : ℕ, ↑kn ≠ -a ∧ ↑kn ≠ -b ∧ ↑kn ≠ -c ∧ ↑kn ≠ -d ∧ ↑kn ≠ -e) {z : 𝔸} (hz : ‖z‖ < 1) :
    HasSum (fun n ↦ hypergeometric₃F₂Coefficient a b c d e n • z ^ n) (₃F₂ a b c d e z) := by
  have hmem : z ∈ Metric.eball (0 : 𝔸) 1 := by
    rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm]
    exact ENNReal.ofReal_lt_one.mpr hz
  have := (hypergeometric₃F₂_hasFPowerSeriesOnBall 𝔸 a b c d e h).hasSum hmem
  simpa only [hypergeometric₃F₂Series_apply_eq, zero_add] using this

/-- `₃F₂` is analytic on the open unit ball. -/
theorem hypergeometric₃F₂_analyticOnNhd
    (h : ∀ kn : ℕ, ↑kn ≠ -a ∧ ↑kn ≠ -b ∧ ↑kn ≠ -c ∧ ↑kn ≠ -d ∧ ↑kn ≠ -e) :
    AnalyticOnNhd 𝕂 (₃F₂ a b c d e) (Metric.eball (0 : 𝔸) 1) := fun _ hy ↦
  (hypergeometric₃F₂_hasFPowerSeriesOnBall 𝔸 a b c d e h).analyticAt_of_mem hy

end RCLike
