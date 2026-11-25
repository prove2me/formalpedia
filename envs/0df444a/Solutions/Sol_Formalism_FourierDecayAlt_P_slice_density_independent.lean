-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.slice_density_independent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:06:42.526563+00:00
-- url     : https://prove2.me/submissions/7106f326-e81b-436e-aefa-129b729d4116

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LinearChangeOfVariablesBis
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourthWeightDensityOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JacobianAeNonzero
import Theorems.Thm_Formalism_FourierDecayAlt_P_rootCOV_statement
import Theorems.Thm_Formalism_FourierDecayAlt_P_fourth_weight_density_of_parts
import Theorems.Thm_Formalism_FourierDecayAlt_P_linear_change_of_variables_bis


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt MeasureTheory
open scoped ENNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open RootChangeOfVariables
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C2.SliceDensityIndependent := fourth_weight_density_of_parts rootCOV_statement linear_change_of_variables_bis
end Formalism.FourierDecayAlt.P
