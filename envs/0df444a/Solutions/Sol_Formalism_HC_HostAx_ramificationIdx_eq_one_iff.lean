-- Prove2me | solution 1 for Formalism.HC.HostAx.ramificationIdx_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:07:56.657553+00:00
-- url     : https://prove2.me/submissions/8e750484-e937-4b25-8916-115ae50120e5

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostRam
import Theorems.Thm_Formalism_FrobeniusOrbits_SplitK_span_prime


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
open Formalism.HC.HostAx
variable {φ : Frame} (H : HostAx φ)
namespace Formalism.HC.HostAx
theorem _root_.solution (p : ℕ) [hp : Fact p.Prime]
    (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] :
    P.ramificationIdx ℤ = 1 ↔ ∀ σ : H.E ≃ₐ[ℚ] H.E, (∀ x : 𝓞 H.E, σ • x - x ∈ P) → σ = 1 := by
  have := H.galois
  have : IsGaloisGroup Gal(H.E/ℚ) ℤ (𝓞 H.E) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ H.E
  have := SplitK.span_prime p
  rw [← ramificationIdxIn_eq_ramificationIdx (span {(p : ℤ)}) P Gal(H.E/ℚ),
    ← card_inertia_eq_ramificationIdxIn (G := Gal(H.E/ℚ)) (span {(p : ℤ)}) P, Subgroup.card_eq_one,
    Subgroup.eq_bot_iff_forall]
  rfl
end Formalism.HC.HostAx
