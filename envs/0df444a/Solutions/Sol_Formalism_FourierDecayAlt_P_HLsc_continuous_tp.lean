-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HLsc.continuous_tp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:30:37.246398+00:00
-- url     : https://prove2.me/submissions/ed336a4a-40a2-4203-9618-bbc90430e8fa

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Herglotz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HerglotzLowerSemicontinuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_continuous_ee

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HLsc
open Real Filter Topology Finset MeasureTheory Formalism.FourierDecayAlt.P.Herglotz
variable {d : ℕ}
namespace Formalism.FourierDecayAlt.P.HLsc
theorem _root_.solution (B : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ) : Continuous (tp B c) := by
  unfold tp
  exact continuous_finsetSum _ (fun σ _ => continuous_const.mul (continuous_ee σ))
end Formalism.FourierDecayAlt.P.HLsc
