-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.HomD_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:49:24.075322+00:00
-- url     : https://prove2.me/submissions/8f249fb3-683d-48ac-b53f-999bfc5165b8

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SegDefs
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ExistsMonomialOrder
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_IntegralMonomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] {L L' : Type} {r : ℕ}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {κ : Type} (s : Finset κ) (d : κ → L → ℕ) (f : κ → MvPolynomial (L × Fin r) K)
    (h : ∀ k ∈ s, HomD (d k) (f k)) : HomD (fun i => ∑ k ∈ s, d k i) (∏ k ∈ s, f k) := by
  classical
  have hadd : ∀ (β γ : L × Fin r →₀ ℕ) (i : L), ldeg (β + γ) i = ldeg β i + ldeg γ i := by
    intro β γ i
    simp [ldeg, Finset.sum_add_distrib]
  have hmul : ∀ (d₁ d₂ : L → ℕ) (F G : MvPolynomial (L × Fin r) K), HomD d₁ F → HomD d₂ G →
      HomD (fun i => d₁ i + d₂ i) (F * G) := by
    intro d₁ d₂ F G hF hG β hβ i
    obtain ⟨β₁, h₁, β₂, h₂, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul F G hβ)
    rw [hadd, hF β₁ h₁ i, hG β₂ h₂ i]
  induction s using Finset.induction_on with
  | empty =>
    intro β hβ i
    simp only [Finset.prod_empty, MvPolynomial.support_one, Finset.mem_singleton] at hβ
    subst hβ
    simp [ldeg]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have e : (fun i => ∑ k ∈ insert a s, d k i) = fun i => d a i + ∑ k ∈ s, d k i := by
      funext i
      rw [Finset.sum_insert ha]
    rw [e]
    exact hmul _ _ _ _ (h a (Finset.mem_insert_self a s))
      (ih (fun k hk => h k (Finset.mem_insert_of_mem hk)))
end Formalism.MainNotions.PlaneGram
