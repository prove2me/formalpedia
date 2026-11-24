-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.dual_lattice_subset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:41.587593+00:00
-- url     : https://prove2.me/submissions/00644e57-8a48-4029-898b-c312400bce50

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualIdealInclusion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualVolumePowerIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_powConjStable
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_between
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_dualSubset
import Theorems.Thm_Formalism_FourierDecayAlt_P_dual_third_group_holds


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
theorem _root_.solution : Formalism.FourierDecayAlt.S6.DualSubset :=
  dualSubset dual_third_group_holds powConjStable between
end Formalism.FourierDecayAlt.P
