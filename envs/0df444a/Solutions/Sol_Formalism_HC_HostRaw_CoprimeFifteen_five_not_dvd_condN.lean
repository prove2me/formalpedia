-- Prove2me | solution 1 for Formalism.HC.HostRaw.CoprimeFifteen.five_not_dvd_condN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:58:26.503646+00:00
-- url     : https://prove2.me/submissions/59e9ab73-c37c-4ca4-9cd8-2459d0701166

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ConjEMemHostFIff
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_SplitK
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ExistsOpenNormalOrderOf
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Theorems.Thm_Formalism_HC_HostRaw_q_mod_eight
import Theorems.Thm_Formalism_HC_HostRaw_d_mod_sixteen
import Theorems.Thm_Formalism_HC_HostRaw_not_dvd_condN_iff
import Theorems.Thm_Formalism_HC_HostRaw_CoprimeFifteen_five_not_dvd_QS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC
open Formalism.FrobeniusOrbits
open Formalism.HC.HostRaw
variable {φ : Frame} (H : HostRaw φ)
variable {H}
namespace Formalism.HC.HostRaw
namespace CoprimeFifteen
theorem _root_.solution (h : H.CoprimeFifteen) : ¬ 5 ∣ H.condN := by
  exact (H.not_dvd_condN_iff Nat.prime_five).2 ⟨h.five_not_dvd_QS,
    fun e => by have := H.q_mod_eight; omega, fun e => by have := H.d_mod_sixteen; omega⟩
end CoprimeFifteen
end Formalism.HC.HostRaw
