-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxB.cvRho_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:12:53.43662+00:00
-- url     : https://prove2.me/submissions/907c3fda-33e0-41e6-bea4-57f1ef4fd72f

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_cvLeft
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_cvPost
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_cvRight_of
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_cvRhoOfParts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxB
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.JFxB
theorem _root_.solution (hA : CapAdInv) : JF.CVRho := cvRhoOfParts cvLeft (cvRight_of hA) cvPost
end Formalism.FourierDecayAlt.P.JFxB
