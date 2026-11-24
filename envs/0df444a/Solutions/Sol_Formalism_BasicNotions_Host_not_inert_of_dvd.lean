-- Prove2me | solution 1 for Formalism.BasicNotions.Host.not_inert_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:29:28.346311+00:00
-- url     : https://prove2.me/submissions/1fc04e4e-78bb-4415-b30d-2d1886c5414f

import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_DvdCondNIffCls
import Theorems.Thm_Formalism_BasicNotions_Host_dvd_condN_iff_cls
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
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Host
variable {R : Ranks} (H : Host R)
namespace Formalism.BasicNotions.Host
theorem _root_.solution {p : ℕ} (hp : p.Prime) (h : p ∣ H.condN) :
    ¬ (H.cls p = .inertClass ∨ H.cls p = .signal) := by
  rcases (dvd_condN_iff_cls H hp).mp h with h1 | h1 | h1 <;> rw [h1] <;> simp
end Formalism.BasicNotions.Host
