-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LevelGrowthBounds.Pp_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:17.684069+00:00
-- url     : https://prove2.me/submissions/3f56b948-7ca0-4853-bd37-11ee30a8ce8e

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
theorem _root_.solution {e : ℕ → ℝ} (he : ∀ i, 0 ≤ e i) (i : ℕ) :
    Pp e i ^ 2 = ∏ l ∈ Icc 1 i, (1 + e l) := by
  unfold Pp
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro l _
  rw [Real.sq_sqrt (by linarith [he l])]
end Formalism.FourierDecayAlt.P.LevelGrowthBounds
