-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxE.cVRho
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:23:11.863047+00:00
-- url     : https://prove2.me/submissions/f8c444b2-b222-42cd-b974-3064acaee83c

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EHcChange
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapAdInv
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_capAdInv
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_cvRho_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxE
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.JFxB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.JFxE
theorem _root_.solution : JF.CVRho := cvRho_of capAdInv
end Formalism.FourierDecayAlt.P.JFxE
