-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.level_groups_are_subgroups
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:42:56.680564+00:00
-- url     : https://prove2.me/submissions/28fe5e07-12ed-4e75-ad10-926f5b003136

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x1_gpOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x1_gpUni
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x1_par_subgroupSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x1_emb_subgroupSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x1_isN_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x1_isNU_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x1_subgroupSet_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x1_pointwise_stabiliser_is_subgroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Formalism.FourierDecayAlt.P.S3x1
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.S3.GroupsAreGroups := by
  intro A _ r k
  exact ⟨subgroupSet_congr isN_iff (par_subgroupSet gpOne), emb_subgroupSet gpUnit,
    emb_subgroupSet gpUni, subgroupSet_congr isS_iff (par_subgroupSet gpUnit),
    subgroupSet_congr isNU_iff (par_subgroupSet gpUni), pointwise_stabiliser_is_subgroup⟩
end Formalism.FourierDecayAlt.P
