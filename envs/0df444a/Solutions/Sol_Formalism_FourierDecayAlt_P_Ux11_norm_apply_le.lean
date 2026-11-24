-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux11.norm_apply_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:28:25.804752+00:00
-- url     : https://prove2.me/submissions/f81514da-0ea6-4039-a9da-cde069218ae7

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakToStrongSmoothnessReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Set
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux11
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Formalism.FourierDecayAlt.P.Ux11
theorem _root_.solution {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (h : X) (hh : ‖h‖ ≤ 1) :
    ‖ContinuousLinearMap.apply ℝ F h‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun T => by
    rw [ContinuousLinearMap.apply_apply, one_mul]
    exact (T.le_opNorm h).trans (mul_le_of_le_one_right (norm_nonneg _) hh))
end Formalism.FourierDecayAlt.P.Ux11
