-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero.cutM_one_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:52:41.39503+00:00
-- url     : https://prove2.me/submissions/3b9c9d0b-96ac-436b-885f-9a23681dc11f

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WhittakerVanishingImpliesZero
import Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_cutM_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_cutM_contDiff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero
theorem _root_.solution (s j : ℕ) : ∃ C : ℝ, ∀ Z : Mat s, ‖iteratedFDeriv ℝ j (cutM 1) Z‖ ≤ C := by
  have hc : HasCompactSupport (cutM (s := s) 1) :=
    HasCompactSupport.intro (isCompact_closedBall 0 2) fun Z hZ => cutM_eq_zero one_pos (by
      rw [Metric.mem_closedBall, dist_zero_right, not_le] at hZ
      linarith)
  exact ((cutM_contDiff 1 (n := j)).continuous_iteratedFDeriv le_rfl).bounded_above_of_compact_support
    (hc.iteratedFDeriv j)
end Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero
