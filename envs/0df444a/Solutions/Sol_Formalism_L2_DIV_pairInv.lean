-- Prove2me | solution 1 for Formalism.L2.DIV.pairInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:24:50.160873+00:00
-- url     : https://prove2.me/submissions/7e13576e-6760-493e-b350-95b3e217b99c

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas
import Theorems.Thm_Formalism_L2_DIV_pairTransport
import Theorems.Thm_Formalism_L2_DIV_pairK_apply
import Theorems.Thm_Formalism_L2_DIV_rhoK_coe
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open MvPolynomial NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.BasicNotions
namespace Formalism.L2.DIV
theorem _root_.solution : PairInv := by
  intro K _ _ ι _ n lam G g hg x y
  rw [pairK_apply, pairK_apply, rhoK_coe, rhoK_coe, pairTransport K ι n lam G g g x.1 y.1]
  simp only [hg]
end Formalism.L2.DIV
