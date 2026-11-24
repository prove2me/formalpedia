-- Prove2me | solution 1 for Formalism.HC.HostRaw.not_dvd_condN_of_inert
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:55:08.137379+00:00
-- url     : https://prove2.me/submissions/fcfd7718-bc81-4bf9-8d8b-e3e4672d8f36

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ConjEMemHostFIff
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_SplitK
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ExistsOpenNormalOrderOf
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Theorems.Thm_Formalism_HC_HostRaw_not_dvd_condN_iff
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC
open Formalism.FrobeniusOrbits
open Formalism.HC.HostRaw
variable {φ : Frame} (H : HostRaw φ)
namespace Formalism.HC.HostRaw
theorem _root_.solution {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (hj : jacobiSym (-(H.d : ℤ)) p = -1) :
    ¬ p ∣ H.condN := by
  rw [H.not_dvd_condN_iff hp]
  refine ⟨fun hd => ?_, fun hq => ?_, fun hd => ?_⟩
  · rw [H.QS_split p hp h2 hd] at hj
    norm_num at hj
  · subst hq
    rw [H.hyp.2.2.2.2] at hj
    norm_num at hj
  · subst hd
    rw [jacobiSym.mod_left, show (-(H.d : ℤ)) % (H.d : ℤ) = 0 by simp,
      jacobiSym.zero_left H.d_prime.one_lt] at hj
    norm_num at hj
end Formalism.HC.HostRaw
