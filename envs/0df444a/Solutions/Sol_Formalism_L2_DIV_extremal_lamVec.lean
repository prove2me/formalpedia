-- Prove2me | solution 1 for Formalism.L2.DIV.extremal_lamVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:11:43.794303+00:00
-- url     : https://prove2.me/submissions/235c007d-5df5-4d96-92ba-652bac8573cb

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas
import Theorems.Thm_Formalism_L2_DIV_lamVec_natW
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
variable {K : Type} [Field K]
namespace Formalism.L2.DIV
theorem _root_.solution : extremal K 2 lamVec = X (0, 0) := by
  unfold extremal Formalism.GradedWeylDivisibility.hw
  rw [lamVec_natW, Fin.prod_univ_two]
  simp [Formalism.GradedWeylDivisibility.nuNext, Formalism.GradedWeylDivisibility.lpMinor]
end Formalism.L2.DIV
