-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LevelGrowthBounds.pow_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:40.902844+00:00
-- url     : https://prove2.me/submissions/f05b55ab-cd21-4c0b-b268-189bf4ad09eb

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelGrowthBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LevelGrowthBounds
open Finset Real
namespace Formalism.FourierDecayAlt.P.LevelGrowthBounds
theorem _root_.solution (r : ℕ) (η : ℝ) (hη : 0 ≤ η) (hx : ((r:ℝ) + 1) * η ≤ 1 / 2) :
    ((1 + η) ^ (r+1)) ^ 2 ≤ 1 + 4 * ((r:ℝ) + 1) * η := by
  have hx0 : 0 ≤ ((r:ℝ) + 1) * η := by positivity
  have h1 : 1 + η ≤ Real.exp η := by
    have := Real.add_one_le_exp η; linarith
  have h2 : ((1 + η) ^ (r+1)) ^ 2 ≤ Real.exp (2 * (((r:ℝ) + 1) * η)) := by
    rw [← pow_mul]
    have h3 : Real.exp (2 * (((r:ℝ) + 1) * η)) = Real.exp η ^ ((r+1) * 2) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [h3]
    exact pow_le_pow_left₀ (by linarith) h1 _
  have hy0 : 0 ≤ 2 * (((r:ℝ) + 1) * η) := by linarith
  have hE := Real.abs_exp_sub_one_le (x := 2 * (((r:ℝ) + 1) * η))
    (by rw [abs_of_nonneg hy0]; linarith)
  rw [abs_of_nonneg hy0] at hE
  have hE' := le_abs_self (Real.exp (2 * (((r:ℝ) + 1) * η)) - 1)
  nlinarith
end Formalism.FourierDecayAlt.P.LevelGrowthBounds
