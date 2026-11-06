-- Prove2me | solution 1 for BianchiIX.core_radius_budget
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:32:23.448083+00:00
-- url     : https://prove2.me/submissions/c2f7c3fc-4223-4878-96da-3d480f9da937

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

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreBootstrap_wall_bound {k u : ℝ} (hk : 6 ≤ k) (hu : u ≤ (1 / 10000) / k) :
    u ≤ 1 / 60000 := by
  have hk0 : 0 < k := by linarith
  exact hu.trans ((div_le_iff₀ hk0).mpr (by linarith))

end
end

theorem solution {k u w : ℝ} (hk : 6 ≤ k)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k) (hw : 0 ≤ w ∧ w ≤ (1 / 10000) / k) :
    (14 * u / k + 4 * u * w / k + 3 * u ^ 2 / k ^ 2 + 4 * w ^ 2 / k) / (999 / 1000) ≤
      16 / k * (u + w ^ 2) := by
  have hk0 : 0 < k := by linarith
  have hu' := coreBootstrap_wall_bound hk hu.2
  have hw' := coreBootstrap_wall_bound hk hw.2
  have huw : u * w ≤ u / 60000 := by nlinarith [mul_nonneg hu.1 (sub_nonneg.mpr hw')]
  have huu : u ^ 2 ≤ u / 60000 := by nlinarith [mul_nonneg hu.1 (sub_nonneg.mpr hu')]
  have huuk : u ^ 2 / k ≤ u / 60000 :=
    (div_le_self (sq_nonneg u) (by linarith : 1 ≤ k)).trans huu
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 999 / 1000)).mpr
  apply (mul_le_mul_iff_right₀ hk0).mp
  field_simp
  nlinarith [sq_nonneg w, mul_nonneg hu.1 (show 0 ≤ k - 6 by linarith),
    mul_nonneg (show 0 ≤ u / 60000 - u * w by linarith) hk0.le]
