-- Prove2me | solution 1 for Formalism.L2.DIV.pairingExtremal_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:46:57.934428+00:00
-- url     : https://prove2.me/submissions/7a90d1f3-b8e8-4410-bcff-eefd911bd93a

import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkMapInitMinor
import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkPderivBlockEmbNe
import Theorems.Thm_Formalism_L2_DIV_fockSymTensor_holds
import Theorems.Thm_Formalism_L2_DIV_extNormPos
import Theorems.Thm_Formalism_L2_DIV_pairExtremal_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open scoped Matrix
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.BasicNotions
namespace Formalism.L2.DIV
theorem _root_.solution : PairExtremal := pairExtremal_of fockSymTensor_holds extNormPos
end Formalism.L2.DIV
