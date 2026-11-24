-- Prove2me | solution 1 for Formalism.HC.Der.cmType
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:33:59.150852+00:00
-- url     : https://prove2.me/submissions/ea253a7d-a549-43fa-9490-42907fc44681

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycGrp
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycAll
import Theorems.Thm_Formalism_HC_Der_cmType_iff
import Theorems.Thm_Formalism_FrobeniusOrbits_Final_cmType
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Der_finrank_E
import Theorems.Thm_Formalism_HC_Der_gal_mem_Psi_iff
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
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits
variable {φ : Frame} (H : HostRaw φ)
namespace Formalism.HC.Der
theorem _root_.solution : (∀ ψ : H.E →+* ℂ, ψ ∈ H.cmType ↔ (starRingEnd ℂ).comp ψ ∉ H.cmType) ∧ H.cmType.ncard = 2 * φ.ord ∧
    ∀ ψ ∈ H.cmType, ∀ σ : H.E ≃ₐ[ℚ] H.E, ψ.comp (σ : H.E →+* H.E) ∈ H.cmType ↔ H.gal σ ∈ φ.Psi := by
  refine ⟨cmType_iff H, ?_, fun ψ hψ σ => ?_⟩
  · have hinv : Function.Involutive (fun ψ : H.E →+* ℂ => (starRingEnd ℂ).comp ψ) := fun ψ => by
      ext x
      simp
    have h1 : H.cmTypeᶜ = (fun ψ : H.E →+* ℂ => (starRingEnd ℂ).comp ψ) '' H.cmType := by
      ext ψ
      constructor
      · intro h
        refine ⟨_, (cmType_iff H ((starRingEnd ℂ).comp ψ)).mpr ?_, hinv ψ⟩
        have h2 : (starRingEnd ℂ).comp ((starRingEnd ℂ).comp ψ) = ψ := hinv ψ
        rwa [h2]
      · rintro ⟨χ, h2, rfl⟩
        exact (cmType_iff H χ).mp h2
    have h2 := Set.ncard_add_ncard_compl H.cmType
    rw [h1, Set.ncard_image_of_injective _ hinv.injective, Nat.card_eq_fintype_card, Embeddings.card,
      finrank_E] at h2
    omega
  · rw [gal_mem_Psi_iff]
    have h1 : ψ H.sqd = _ := hψ
    show ψ (σ H.sqd) = _ ↔ _
    rw [← h1]
    exact ψ.injective.eq_iff
end Formalism.HC.Der
