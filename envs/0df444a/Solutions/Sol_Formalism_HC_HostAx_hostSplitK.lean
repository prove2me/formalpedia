-- Prove2me | solution 1 for Formalism.HC.HostAx.hostSplitK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:58:05.215885+00:00
-- url     : https://prove2.me/submissions/f7f3f171-8ed2-47b9-b8b8-0930a16f2c46

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ConjEMemHostFIff
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_SplitK
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ExistsOpenNormalOrderOf
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Theorems.Thm_Formalism_HC_HostRaw_ne_two_of_not_dvd
import Theorems.Thm_Formalism_HC_HostRaw_ncard_primesOver_d
import Theorems.Thm_Formalism_HC_HostAx_frob_mem_Psi_iff
import Theorems.Thm_Formalism_HC_HostAx_splitK_of_dvd
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
theorem _root_.solution :
    (∀ p : ℕ, p.Prime →
      ((primesOver (span {(p : ℤ)}) (𝓞 H.K)).ncard = 2 ↔ (p = 2 ∨ (p ≠ 2 ∧ jacobiSym (-(H.d : ℤ)) p = 1)))) ∧
    (primesOver (span {(H.d : ℤ)}) (𝓞 H.K)).ncard = 1 ∧
    (primesOver (span {(H.q : ℤ)}) (𝓞 H.K)).ncard = 2 ∧
    ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ H.condN →
    ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E), IsArithFrobAt ℤ σ P →
      (H.galE σ ∈ φ.Psi ↔ (primesOver (span {(p : ℤ)}) (𝓞 H.K)).ncard = 2) := by
  refine ⟨H.der.splitK, H.ncard_primesOver_d, H.splitK_of_dvd H.q_prime (dvd_mul_left _ _), ?_⟩
  intro p _ hp P _ _ σ hσ
  rw [H.frob_mem_Psi_iff p hp P σ hσ, H.der.splitK p Fact.out]
  simp [H.ne_two_of_not_dvd hp]
end Formalism.HC.HostAx
