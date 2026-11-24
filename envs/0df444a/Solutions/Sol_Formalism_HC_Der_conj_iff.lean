-- Prove2me | solution 1 for Formalism.HC.Der.conj_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:08:08.012833+00:00
-- url     : https://prove2.me/submissions/09f23056-c2c4-44be-aaf8-24e8b0d17ef0

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DecompTypeI
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSymOfModEq
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycBasic
import Theorems.Thm_Formalism_HC_Der_gal_conj
import Theorems.Thm_Formalism_HC_Der_conj_apply
import Theorems.Thm_Formalism_FrobeniusOrbits_Final_conj


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
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits
variable {φ : Frame} (H : HostRaw φ)
namespace Formalism.HC.Der
theorem _root_.solution : ∀ (ψ : H.E →+* ℂ) (σ : H.E ≃ₐ[ℚ] H.E),
    (∀ x, ψ (σ x) = starRingEnd ℂ (ψ x)) ↔ H.gal σ = φ.cc := by
  intro ψ σ
  constructor
  · intro h
    have h1 : σ = H.conj := AlgEquiv.ext fun x => ψ.injective (by rw [h, conj_apply])
    rw [h1, gal_conj]
  · intro h x
    have h1 : σ = H.conj := H.gal.injective (h.trans (gal_conj H).symm)
    rw [h1, conj_apply]
end Formalism.HC.Der
