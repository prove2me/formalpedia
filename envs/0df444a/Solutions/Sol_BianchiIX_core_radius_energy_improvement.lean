-- Prove2me | solution 1 for BianchiIX.core_radius_energy_improvement
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:32:25.390229+00:00
-- url     : https://prove2.me/submissions/d9c41295-25f4-4f63-85dd-28395a912b69

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

theorem solution {k r u w : ℝ} (hk : 6 ≤ k)
    (hr : 0 ≤ r) (hrhi : r ≤ 101 / 100 * k)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k) (hw : 0 ≤ w ∧ w ≤ (1 / 10000) / k)
    (hR : |r - k| ≤ 16 / k * (u + w ^ 2)) : |r ^ 2 - k ^ 2| < 1 / 16 := by
  have hk0 : 0 < k := by linarith
  have hu' := coreBootstrap_wall_bound hk hu.2
  have hw' := coreBootstrap_wall_bound hk hw.2
  have hw2 := (sq_le_sq₀ hw.1 (by norm_num : (0 : ℝ) ≤ 1 / 60000)).mpr hw'
  have hnonneg : 0 ≤ 16 / k * (u + w ^ 2) :=
    mul_nonneg (by positivity) (add_nonneg hu.1 (sq_nonneg w))
  calc
    |r ^ 2 - k ^ 2| = |r - k| * (r + k) := by
      rw [show r ^ 2 - k ^ 2 = (r - k) * (r + k) by ring, abs_mul, abs_of_nonneg (by linarith : 0 ≤ r + k)]
    _ ≤ (16 / k * (u + w ^ 2)) * (201 / 100 * k) :=
      mul_le_mul hR (by linarith) (by linarith) hnonneg
    _ = (804 / 25) * (u + w ^ 2) := by field_simp; ring
    _ < 1 / 16 := by nlinarith
