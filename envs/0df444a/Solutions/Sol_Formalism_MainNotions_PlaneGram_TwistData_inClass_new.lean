-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.inClass_new
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:53:03.24592+00:00
-- url     : https://prove2.me/submissions/32dfc9b1-791b-40d1-8758-f64139a0a822

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_onLetter_apply
import Theorems.Thm_Formalism_MainNotions_PlaneGram_letE_apply
import Theorems.Thm_Formalism_MainNotions_PlaneGram_offE_apply
import Theorems.Thm_Formalism_MainNotions_PlaneGram_divE_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.PlaneGram.letE_apply
attribute [local simp] Formalism.MainNotions.PlaneGram.divE_apply

set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K]
open Formalism.MainNotions.PlaneGram.TwistData
variable (D : TwistData K) (p : ℕ)
variable (t : D.Tau)
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution (ρ'' : D.Tau → Fin D.r → ℕ) (α : D.EA) (ρ1 x : Fin D.r →₀ ℕ) :
    D.InClass p ρ'' (offE (Sum.inr t) α + onLetter (Sum.inr t) (ρ1 + D.P p t • x)) ↔
      (∀ a, ρ1 a % D.P p t = ρ'' t a) ∧
        ∀ t', t' ≠ t → ∀ a, α (Sum.inr t', a) % D.P p t' = ρ'' t' a := by
  have hval : ∀ t' a, ((Formalism.MainNotions.PlaneGram.offE (Sum.inr t) α + onLetter (Sum.inr t) (ρ1 + D.P p t • x) : D.EA)) (Sum.inr t', a) =
      if t' = t then ρ1 a + D.P p t * x a else α (Sum.inr t', a) := by
    intro t' a
    rw [Finsupp.add_apply, Formalism.MainNotions.PlaneGram.offE_apply, onLetter_apply]
    by_cases h : t' = t
    · subst h
      simp
    · have hne : (Sum.inr t' : D.OL) ≠ Sum.inr t := fun e => h (Sum.inr_injective e)
      simp [h, hne]
  constructor
  · intro h
    refine ⟨fun a => ?_, fun t' ht' a => ?_⟩
    · have h1 := h t a
      rw [hval, if_pos rfl, Nat.add_mul_mod_self_left] at h1
      exact h1
    · have h1 := h t' a
      rw [hval, if_neg ht'] at h1
      exact h1
  · rintro ⟨h1, h2⟩ t' a
    rw [hval]
    by_cases h : t' = t
    · subst h
      rw [if_pos rfl, Nat.add_mul_mod_self_left]
      exact h1 a
    · rw [if_neg h]
      exact h2 t' h a
end Formalism.MainNotions.PlaneGram.TwistData
