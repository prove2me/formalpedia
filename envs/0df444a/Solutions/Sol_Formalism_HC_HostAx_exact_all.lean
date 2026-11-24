-- Prove2me | solution 1 for Formalism.HC.HostAx.exact_all
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:19:04.51691+00:00
-- url     : https://prove2.me/submissions/d9c29837-0215-4874-9b30-018aa36cc74f

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostRam
import Theorems.Thm_Formalism_HC_HostRaw_condN_div_q
import Theorems.Thm_Formalism_HC_HostRaw_condN_div_d
import Theorems.Thm_Formalism_HC_HostRaw_PsQ_exists_q
import Theorems.Thm_Formalism_HC_HostAx_exists_d
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
open Formalism.HC.HostAx
variable {φ : Frame} (H : HostAx φ)
namespace Formalism.HC.HostAx
theorem _root_.solution (hP : H.PsQ) (hE : H.Exact) (l : ℕ) (hl : l.Prime) (h : l ∣ H.condN) :
    ∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD H.condN / l] ∧ H.art u ≠ 1 := by
  obtain ⟨hq, hd, -, -, -⟩ := H.hyp
  rcases (Nat.Prime.dvd_mul hl).mp h with h' | h'
  · rcases (Nat.Prime.dvd_mul hl).mp h' with h'' | h''
    · exact hE l hl h''
    · rw [(Nat.prime_dvd_prime_iff_eq hl hq).mp h'', HostRaw.condN_div_q]
      obtain ⟨u, hu1, hu2⟩ := hP.exists_q
      refine ⟨u, hu1, fun h1 => ?_⟩
      have h3 := congrArg (fun x : ℤˣ => (x : ℤ)) hu2
      rw [h1] at h3
      simp at h3
  · rw [(Nat.prime_dvd_prime_iff_eq hl hd).mp h', HostRaw.condN_div_d]
    obtain ⟨u, hu1, hu2⟩ := exists_d H
    refine ⟨u, hu1, fun h1 => ?_⟩
    have h3 := congrArg (fun g : φ.GG => ((g.1.2 : ℤˣ) : ℤ)) (hu2.symm.trans h1)
    simp [Frame.iod] at h3
end Formalism.HC.HostAx
