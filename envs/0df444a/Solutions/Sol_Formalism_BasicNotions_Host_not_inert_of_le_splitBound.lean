-- Prove2me | solution 1 for Formalism.BasicNotions.Host.not_inert_of_le_splitBound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:33:58.827868+00:00
-- url     : https://prove2.me/submissions/93553b24-755b-4371-8ede-9ab048eb4a89

import Definitions.Def_Formalism_LocalRingCardinality_HostCls
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_NotInert
import Theorems.Thm_Formalism_BasicNotions_Host_cls_ne_signal_of_jacobi
import Theorems.Thm_Formalism_BasicNotions_Host_primeClass_ne_of_jacobi_one
import Theorems.Thm_Formalism_BasicNotions_primeClass_two
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open Formalism.HC
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Host
variable {R : Ranks} (H : Host R) {p : ℕ}
namespace Formalism.BasicNotions.Host
theorem _root_.solution (hp : p.Prime) (h : p ≤ H.splitBound) :
    ¬ (H.cls p = .signal ∨ H.cls p = .inertClass) := by
  by_cases h2 : p = 2
  · subst h2
    have e : H.cls 2 = .ram2 := primeClass_two H.toHostRaw
    rw [e]
    simp
  · have hj := H.split_small p hp h2 h
    rintro (e | e)
    · exact H.cls_ne_signal_of_jacobi hj e
    · exact H.primeClass_ne_of_jacobi_one hj e
end Formalism.BasicNotions.Host
