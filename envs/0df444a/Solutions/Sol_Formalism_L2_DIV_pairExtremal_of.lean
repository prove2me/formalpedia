-- Prove2me | solution 1 for Formalism.L2.DIV.pairExtremal_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:25:08.027724+00:00
-- url     : https://prove2.me/submissions/887d870a-8f1f-40e3-8139-74952ce89178

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas
import Theorems.Thm_Formalism_L2_DIV_pairP_apply
import Theorems.Thm_Formalism_L2_DIV_pairTransport
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_L2_DIV_fockL_apply
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
theorem _root_.solution : FockSTen → ExtNormPos → PairExtremal := by
  intro hT hP K _ _ _ ι _ n lam G B hB
  rw [pairTransport K ι n lam G B B]
  simp only [hB]
  obtain ⟨q, hq, hq'⟩ := hP K ι n lam
  have hne : extNorm K lam ≠ 0 := by
    rw [hq']
    simpa using hq.ne'
  have h1 : gramTw lam (fun _ : ι => (1 : Matrix (Fin n) (Fin n) K)) = 1 := by
    unfold gramTw
    simp
  rw [pairP_apply, h1]
  simp only [Matrix.transpose_one]
  rw [blockAct_one, AlgHom.id_apply, fockL_apply, hT K ι n]
  exact div_mul_cancel₀ 1 hne |>.trans rfl |> fun h => by simpa [extNorm] using h
end Formalism.L2.DIV
