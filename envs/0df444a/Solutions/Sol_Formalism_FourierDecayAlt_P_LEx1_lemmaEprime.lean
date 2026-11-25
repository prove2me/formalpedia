-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx1.lemmaEprime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:40:46.409828+00:00
-- url     : https://prove2.me/submissions/bec8edb2-4809-42da-aea6-8cdbe210eb1d

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaEprimeFromSteps
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_lemmaEprimeFromSteps
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_epStep6
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_leibniz
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_epStep5
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_cutBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_limit_L2
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_pairLimit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.LEx1
theorem _root_.solution : LemmaEprime :=
  lemmaEprimeFromSteps leibniz cutBound limit_L2 pairLimit epStep5 epStep6
end Formalism.FourierDecayAlt.P.LEx1
