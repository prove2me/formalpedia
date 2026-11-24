-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.chainSet_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:07:15.251378+00:00
-- url     : https://prove2.me/submissions/39037737-e37e-466c-a5b5-cfe32325a8b8

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ProjKeepsLetter
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutedExponentApplyBlock
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_chainSet_mono
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_chainSet_disjoint

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
variable (D : TwistData K)
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution (hch : ∀ j i, D.chain j i ⊆ D.LLj j)
    (hnest : ∀ (j : Fin D.J) (i i' : Fin (D.nch j)), i < i' → D.chain j i ⊂ D.chain j i')
    (x y : Σ j : Fin D.J, Fin (D.nch j)) :
    D.chainSet x.1 x.2 ⊆ D.chainSet y.1 y.2 ∨ D.chainSet y.1 y.2 ⊆ D.chainSet x.1 x.2 ∨
      Disjoint (D.chainSet x.1 x.2) (D.chainSet y.1 y.2) := by
  obtain ⟨j, i⟩ := x
  obtain ⟨j', i'⟩ := y
  by_cases hj : j = j'
  · subst hj
    rcases lt_trichotomy i i' with h | h | h
    · left
      exact D.chainSet_mono j i i' (hnest j i i' h).1
    · left
      rw [h]
    · right; left
      exact D.chainSet_mono j i' i (hnest j i' i h).1
  · right; right
    exact D.chainSet_disjoint hch j j' hj i i'
end Formalism.MainNotions.PlaneGram.TwistData
