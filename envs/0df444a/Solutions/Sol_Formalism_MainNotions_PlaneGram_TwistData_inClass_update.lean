-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.inClass_update
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:53:04.28282+00:00
-- url     : https://prove2.me/submissions/e2ed38e4-e89c-4588-aa47-36356f390c5f

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial

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
variable {K : Type} [Field K]
open Formalism.MainNotions.PlaneGram.TwistData
variable (D : TwistData K) (p : ℕ)
variable (t : D.Tau)
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution (ρ'' : D.Tau → Fin D.r → ℕ) (α : D.EA) (cl : Fin D.r → ℕ) :
    D.InClass p (Function.update ρ'' t cl) α ↔
      (cl = fun a => α (Sum.inr t, a) % D.P p t) ∧
        ∀ t', t' ≠ t → ∀ a, α (Sum.inr t', a) % D.P p t' = ρ'' t' a := by
  constructor
  · intro h
    refine ⟨funext fun a => ?_, fun t' ht' a => ?_⟩
    · have h1 := h t a
      rw [Function.update_apply, if_pos rfl] at h1
      exact h1.symm
    · have h1 := h t' a
      rw [Function.update_apply, if_neg ht'] at h1
      exact h1
  · rintro ⟨h1, h2⟩ t' a
    rw [Function.update_apply]
    by_cases h : t' = t
    · subst h
      rw [if_pos rfl, h1]
    · rw [if_neg h]
      exact h2 t' h a
end Formalism.MainNotions.PlaneGram.TwistData
