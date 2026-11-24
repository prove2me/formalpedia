-- Prove2me | solution 1 for Formalism.L2.DIV.fockSymTensor_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:31:53.174643+00:00
-- url     : https://prove2.me/submissions/a729a891-9776-4253-abf2-30d128604425

import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkMapInitMinor
import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkPderivBlockEmbNe
import Theorems.Thm_Formalism_L2_DIV_fk_fock_prod

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
theorem _root_.solution : FockSTen := by
  intro K _ _ ι _ n f g
  exact fk_fock_prod Finset.univ f g
end Formalism.L2.DIV
