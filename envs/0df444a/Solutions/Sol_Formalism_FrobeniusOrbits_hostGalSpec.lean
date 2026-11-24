-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.hostGalSpec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:39:36.446218+00:00
-- url     : https://prove2.me/submissions/f0585aed-f900-4bff-8f4f-542597586048

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_trace_eq_iff_units
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_hcl_eq_iff
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_apply_theta
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_exists_lift
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_sgn_lift
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_hPart_lift
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_galE_lift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IntermediateField
noncomputable section
namespace Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
namespace Galois
section Roots
variable {K : Type*} [Field K] {N : ℕ} [NeZero N] {ζ : K}
end Roots
section Layer
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
end Layer
section Host
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
end Host
end Galois
open Galois
private theorem apply_eq_sgn_mul_of_apply_sq_eq_sq {K : Type*} [Field K] [Algebra ℚ K] (σ : Gal(K/ℚ)) (x : K)
    (hx : σ (x ^ 2) = x ^ 2) : σ x = ((sgn σ x : ℤ) : K) * x := by
  rw [sgn.eq_1]
  by_cases hs : σ x = x
  · rw [if_pos hs, Units.val_one, Int.cast_one, one_mul, hs]
  · rw [if_neg hs, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_mul]
    rw [map_pow] at hx
    have h2 : (σ x - x) * (σ x + x) = 0 := by linear_combination hx
    rcases mul_eq_zero.1 h2 with h1 | h1
    · exact absurd (sub_eq_zero.1 h1) hs
    · exact eq_neg_of_add_eq_zero_left h1
end Formalism.FrobeniusOrbits
end
end

set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Galois
namespace Formalism.FrobeniusOrbits
theorem _root_.solution : HostGalSpec := by
  unfold HostGalSpec
  intro e q d hqd L _ _ ζ a b h σ
  obtain ⟨τ, hστ⟩ := exists_lift hqd h σ
  have hsq : ∀ y : L, ∀ r : ℕ, y ^ 2 = -(r : L) → τ (y ^ 2) = y ^ 2 := by
    intro y r hy
    rw [hy, map_neg, map_natCast]
  refine ⟨?_, ?_, fun u => ?_, fun τ' hτ' => galE_lift h hτ'⟩
  · rw [galE.eq_1, hστ (aE ζ a b), sgn_lift hστ (aE ζ a b)]
    exact apply_eq_sgn_mul_of_apply_sq_eq_sq τ a (hsq a q h.2.1)
  · rw [galE.eq_1, hστ (bE ζ a b), sgn_lift hστ (bE ζ a b)]
    exact apply_eq_sgn_mul_of_apply_sq_eq_sq τ b (hsq b d h.2.2.1)
  · rw [galE.eq_1]
    show hPart e ζ a b σ = hcl e u ↔ _
    rw [hPart_lift h hστ, hcl_eq_iff, ← trace_eq_iff_units h.1, hστ, ← apply_theta h.1 τ]
    exact Iff.rfl
end Formalism.FrobeniusOrbits
