-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.level_recursion_lower_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:42:00.965604+00:00
-- url     : https://prove2.me/submissions/7963d49c-ef14-4d93-8921-3a2ff8c93ecf

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelGrowthBounds
import Theorems.Thm_Formalism_FourierDecayAlt_P_LevelGrowthBounds_Pp_sq
import Theorems.Thm_Formalism_FourierDecayAlt_P_LevelGrowthBounds_growth
import Theorems.Thm_Formalism_FourierDecayAlt_P_LevelGrowthBounds_pow_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Real Formalism.FourierDecayAlt.P.LevelGrowthBounds
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.F7.LevelRecursionLS := by
  intro r ε δ e a hε hδ hδ2 he ha hrec
  have hg := growth r ε δ e a hε hδ hδ2 he ha hrec
  refine ⟨fun i hi => hg i hi, fun hx => ?_⟩
  have hη : 0 ≤ ε + 2 * δ := by linarith
  have hpb := pow_bound r (ε + 2 * δ) hη hx
  have hsq := pow_le_pow_left₀ (ha (r+1)) (hg (r+1) le_rfl) 2
  have hPs := Pp_sq he (r+1)
  have ha0 : 0 ≤ a 0 ^ 2 := sq_nonneg _
  have hprod : 0 ≤ ∏ i ∈ Icc 1 (r + 1), (1 + e i) := by rw [← hPs]; exact sq_nonneg _
  calc a (r+1) ^ 2 ≤ ((1 + (ε + 2 * δ)) ^ (r+1) * Pp e (r+1) * a 0) ^ 2 := hsq
    _ = ((1 + (ε + 2 * δ)) ^ (r+1)) ^ 2 * (Pp e (r+1) ^ 2) * a 0 ^ 2 := by ring
    _ = ((1 + (ε + 2 * δ)) ^ (r+1)) ^ 2 * (∏ i ∈ Icc 1 (r + 1), (1 + e i)) * a 0 ^ 2 := by
        rw [hPs]
    _ ≤ (1 + 4 * ((r : ℝ) + 1) * (ε + 2 * δ)) * (∏ i ∈ Icc 1 (r + 1), (1 + e i)) * a 0 ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ ha0
        exact mul_le_mul_of_nonneg_right hpb hprod
end Formalism.FourierDecayAlt.P
