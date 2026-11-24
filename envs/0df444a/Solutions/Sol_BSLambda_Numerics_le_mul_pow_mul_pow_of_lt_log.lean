-- Prove2me | solution 1 for BSLambda.Numerics.le_mul_pow_mul_pow_of_lt_log
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:54:05.553139+00:00
-- url     : https://prove2.me/submissions/2f660235-2edf-4c3e-9ca4-17d14953ffb3

module
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Logs

set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.Numerics
namespace BSLambda.Numerics
theorem _root_.solution {p c y₁ y₂ : ℝ} {m n : ℕ} (hp : 0 < p) (hc : 0 < c)
    (hy₁ : 0 < y₁) (hy₂ : 0 < y₂)
    (h : (m : ℝ) * -Real.log y₁ + (n : ℝ) * -Real.log y₂ < Real.log c) :
    p ≤ c * p * y₁ ^ m * y₂ ^ n := by
  refine ((Real.log_lt_log_iff hp (by positivity)).mp ?_).le
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul hc.ne' hp.ne', Real.log_pow, Real.log_pow]
  linarith
end BSLambda.Numerics
