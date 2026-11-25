-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.pn_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:47:34.499394+00:00
-- url     : https://prove2.me/submissions/355f318a-0c7a-41ff-a91a-939cb7881832

import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentBlockMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_norm_of_lemmas
import Theorems.Thm_Formalism_FourierDecayAlt_P_column_identity
import Theorems.Thm_Formalism_FourierDecayAlt_P_jacobian_natural_measure_constant
import Theorems.Thm_Formalism_FourierDecayAlt_P_local_ratio_product


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.PN.NormBound :=
  norm_of_lemmas jacobian_natural_measure_constant local_ratio_product column_identity
end Formalism.FourierDecayAlt.P
