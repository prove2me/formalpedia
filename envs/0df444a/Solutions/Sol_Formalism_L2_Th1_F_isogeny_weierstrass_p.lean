-- Prove2me | solution 1 for Formalism.L2.Th1.F.isogeny_weierstrass_p
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:14:52.099331+00:00
-- url     : https://prove2.me/submissions/c0a75a81-6434-4447-b880-c35df054fb50

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Elliptic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IsogenyP
import Theorems.Thm_Formalism_L2_Th1_F_isogenyWeierstrassP_of_ellipticNoPole
import Theorems.Thm_Formalism_L2_Th1_F_elliptic_no_pole_const


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open IsogenyPAux
namespace Formalism.L2.Th1.F
theorem _root_.solution : IsogenyP := isogenyWeierstrassP_of_ellipticNoPole elliptic_no_pole_const
end Formalism.L2.Th1.F
