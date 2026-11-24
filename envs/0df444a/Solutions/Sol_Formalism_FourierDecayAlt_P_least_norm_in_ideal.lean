-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.least_norm_in_ideal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:53:31.182264+00:00
-- url     : https://prove2.me/submissions/6e29e1e1-16ba-4910-8f22-b3f8d6171939

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualIdealInclusion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualVolumePowerIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_powConjStable
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_between
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_normIdl
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_leastNorm
import Theorems.Thm_Formalism_FourierDecayAlt_P_dual_third_group_holds
import Theorems.Thm_Formalism_FourierDecayAlt_P_norm_lower_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.S6 Formalism.FourierDecayAlt.P.S6x2
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.S6.LeastNorm :=
  leastNorm dual_third_group_holds norm_lower_bound powConjStable between normIdl
end Formalism.FourierDecayAlt.P
