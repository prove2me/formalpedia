-- Prove2me | solution 1 for Formalism.BasicNotions.not_dvd_condN_iff_primeClass
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:31:15.413546+00:00
-- url     : https://prove2.me/submissions/3cc36f36-06bc-4fb2-8a57-b9fc7d085fcf

import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_LocalRingCardinality_HostCls
import Theorems.Thm_Formalism_BasicNotions_dvd_condN_iff_primeClass
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
open NumberField Formalism.FrobeniusOrbits Formalism.HC
open Formalism Formalism.BasicNotions
variable {φ : Frame} (H : HostRaw φ) {p : ℕ}
namespace Formalism.BasicNotions
theorem _root_.solution (hp : p.Prime) : ¬ p ∣ H.condN ↔
    primeClass H p = .splitK ∨ primeClass H p = .signal ∨ primeClass H p = .inertClass := by
  rw [dvd_condN_iff_primeClass H hp]
  unfold primeClass
  split_ifs <;> simp
end Formalism.BasicNotions
