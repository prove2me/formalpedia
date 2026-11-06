-- Prove2me | solution 1 for BianchiIX.core_log_weak_products
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T02:27:24.810738+00:00
-- url     : https://prove2.me/submissions/5836d1f4-b111-476c-92be-56cc027fe202

import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX


theorem solution {r m v c : ℝ} (hr : 5 ≤ r)
    (hm : 0 ≤ m ∧ m ≤ 1 / 100) (hv : 1 ≤ v) (hc : 0 ≤ c ∧ c ≤ 1 / 100) :
    (2 * (1 + c) / r) * (m / r ^ 2) ≤ 1 / r ^ 2 ∧
      (2 * (1 + c) / r) * (2 * m / r ^ 2) ≤ 1 ∧
      (2 * (1 + c) / r) * (2 * m / (v * r ^ 2)) ≤ m / r := by
  have hr0 : 0 < r := by linarith only [hr]
  have hv0 : 0 < v := by linarith only [hv]
  have hcm : (1 + c) * m ≤ 2 * m := mul_le_mul_of_nonneg_right (by linarith only [hc.2]) hm.1
  have hr2 : 4 ≤ r ^ 2 := by nlinarith only [hr]
  constructor
  · apply (mul_le_mul_iff_of_pos_right (pow_pos hr0 3)).mp
    field_simp
    nlinarith only [hcm, hm.2, hr]
  constructor
  · have hr3 : 1 ≤ r ^ 3 := one_le_pow₀ (by linarith only [hr] : 1 ≤ r)
    apply (mul_le_mul_iff_of_pos_right (pow_pos hr0 3)).mp
    field_simp
    nlinarith only [hcm, hm.2, hr3]
  · have hvr : 4 * (1 + c) ≤ v * r ^ 2 := by
      have H := mul_le_mul_of_nonneg_right hv (sq_nonneg r)
      nlinarith only [H, hr, hc.2]
    have H := mul_le_mul_of_nonneg_right hvr hm.1
    apply (mul_le_mul_iff_of_pos_right (mul_pos hv0 (pow_pos hr0 3))).mp
    field_simp
    nlinarith only [H]
