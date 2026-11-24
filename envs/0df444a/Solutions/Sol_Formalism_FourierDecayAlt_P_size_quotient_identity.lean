-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.size_quotient_identity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:04:15.866186+00:00
-- url     : https://prove2.me/submissions/dfd20715-8739-40b4-9122-804de0da5b8c

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualIdealInclusion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualVolumePowerIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_degreeFacts
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_sizeQuotient
import Theorems.Thm_Formalism_FourierDecayAlt_P_least_norm_in_ideal
import Theorems.Thm_Formalism_FourierDecayAlt_P_dual_size_identity


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
theorem _root_.solution : Formalism.FourierDecayAlt.S6.SizeQuotient :=
  sizeQuotient least_norm_in_ideal dual_size_identity degreeFacts
end Formalism.FourierDecayAlt.P
