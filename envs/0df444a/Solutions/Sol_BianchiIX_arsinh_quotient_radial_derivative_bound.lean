-- Prove2me | solution 1 for BianchiIX.arsinh_quotient_radial_derivative_bound
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T06:55:47.962401+00:00
-- url     : https://prove2.me/submissions/73f33b2e-d109-409a-8f1c-a81852c55c6d

import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX


theorem solution {f a : ℝ → ℝ} {f' a' t r M D : ℝ}
    (Hf : HasDerivAt f f' t) (Ha : HasDerivAt a a' t)
    (hr : 0 < r) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hf : |f t| ≤ 2 * M * r) (ha : r / 2 ≤ a t ∧ a t ≤ M * r)
    (hf' : |f'| ≤ 3 * D) (ha' : |a'| ≤ D) :
    DifferentiableAt ℝ (fun x => Real.arsinh (f x / a x)) t ∧
      |deriv (fun x => Real.arsinh (f x / a x)) t| ≤ 20 * M * D / r := by
  have ha0 : 0 < a t := by linarith only [hr, ha.1]
  have HD := Hf.div Ha (ne_of_gt ha0)
  have Hnum : |f' * a t - f t * a'| ≤ 5 * M * D * r := by
    calc
      _ ≤ |f' * a t| + |f t * a'| := by simpa using abs_sub_le (f' * a t) 0 (f t * a')
      _ = |f'| * a t + |f t| * |a'| := by rw [abs_mul, abs_mul, abs_of_pos ha0]
      _ ≤ (3 * D) * (M * r) + (2 * M * r) * D := by
        gcongr
        exact ha.2
      _ = _ := by ring
  have Hquot : |(f' * a t - f t * a') / (a t) ^ 2| ≤ 20 * M * D / r := by
    rw [abs_div, abs_of_nonneg (sq_nonneg (a t))]
    calc
      _ ≤ (5 * M * D * r) / (r / 2) ^ 2 :=
        div_le_div₀ (by positivity) Hnum (by positivity)
          (pow_le_pow_left₀ (by positivity) ha.1 2)
      _ = _ := by field_simp; ring
  have HS := HD.arsinh
  change HasDerivAt (fun x => Real.arsinh (f x / a x)) _ t at HS
  refine ⟨HS.differentiableAt, ?_⟩
  rw [HS.deriv]
  change |(Real.sqrt (1 + (f t / a t) ^ 2))⁻¹ * ((f' * a t - f t * a') / (a t) ^ 2)| ≤ _
  have hsqrt : 1 ≤ Real.sqrt (1 + (f t / a t) ^ 2) :=
    Real.one_le_sqrt.mpr (by nlinarith only [sq_nonneg (f t / a t)])
  calc
    _ = |(f' * a t - f t * a') / (a t) ^ 2| / Real.sqrt (1 + (f t / a t) ^ 2) := by
      rw [abs_mul, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _)]
      ring
    _ ≤ |(f' * a t - f t * a') / (a t) ^ 2| := div_le_self (abs_nonneg _) hsqrt
    _ ≤ _ := Hquot
