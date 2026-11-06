-- Prove2me | solution 1 for BianchiIX.entrance_denom_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T07:44:48.574232+00:00
-- url     : https://prove2.me/submissions/a54620fb-52c9-46ca-90ea-c7b7cf2ec021

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section
open BianchiIX

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connection_denom_bound {m u v w : ℝ}
    (hu : 0 ≤ u ∧ u ≤ 1 / 10000) (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    3 + m ^ 2 - 4 * u ≤ projectiveDenom (-m) u v w ∧ 0 < projectiveDenom (-m) u v w := by
  have H : 3 + m ^ 2 - 4 * u ≤ projectiveDenom (-m) u v w := by
    dsimp [projectiveDenom, curvature]
    nlinarith only [mul_le_mul_of_nonneg_left hv.2 hu.1,
      mul_le_mul_of_nonneg_left hw.2 hu.1, sq_nonneg u, sq_nonneg (v - w)]
  exact ⟨H, by nlinarith only [H, hu.2, sq_nonneg m]⟩

end
end

theorem solution {k m u v w : ℝ} (hk : 7 / 4 ≤ k)
    (hm : 4 / 5 * k ≤ m - 1 ∧ m - 1 ≤ 101 / 100 * k)
    (hu : 0 ≤ u ∧ u ≤ 1 / 10000) (hv : 0 ≤ v ∧ v ≤ 1)
    (hw : 0 ≤ w ∧ w ≤ 1 / 10000) :
    0 < projectiveDenom m u v w ∧ projectiveDenom m u v w ≤ 6 * (k + 1) ^ 2 := by
  have hpos := (connection_denom_bound (m := -m) hu hv ⟨hw.1, by linarith [hw.2]⟩).2
  simp only [neg_neg] at hpos
  refine ⟨hpos, ?_⟩
  have hu2 : u ^ 2 ≤ 1 := (pow_le_pow_left₀ hu.1 (show u ≤ 1 by linarith [hu.2]) 2).trans_eq (by norm_num)
  have hv2 : v ^ 2 ≤ 1 := (pow_le_pow_left₀ hv.1 hv.2 2).trans_eq (by norm_num)
  have hw2 : w ^ 2 ≤ 1 := (pow_le_pow_left₀ hw.1 (show w ≤ 1 by linarith [hw.2]) 2).trans_eq (by norm_num)
  have hm0 : 0 ≤ m := by linarith [hm.1]
  have hmsq := mul_nonneg (show 0 ≤ 2 * (k + 1) - m by linarith [hm.2])
    (show 0 ≤ 2 * (k + 1) + m by linarith)
  unfold projectiveDenom curvature
  nlinarith only [hmsq, hu2, hv2, hw2, mul_nonneg hu.1 hv.1, mul_nonneg hv.1 hw.1,
    mul_nonneg hw.1 hu.1, sq_nonneg (k - 1), hk]
