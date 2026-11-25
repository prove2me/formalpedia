-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.lemmaEprime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:55:29.290954+00:00
-- url     : https://prove2.me/submissions/6fafa432-7f69-4573-b658-aeebc9c82f32

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaLimit
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_lemmaEprimeFromSteps
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_epStep6
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_leibniz
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_epStep5
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_cutBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_limit_L2
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_pairLimit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.LEx2
theorem _root_.solution : LemmaEprime :=
  lemmaEprimeFromSteps leibniz cutBound limit_L2 pairLimit epStep5 epStep6
end Formalism.FourierDecayAlt.P.LEx2
