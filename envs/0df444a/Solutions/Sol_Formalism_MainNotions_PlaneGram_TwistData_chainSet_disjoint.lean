-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.chainSet_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:51:22.712738+00:00
-- url     : https://prove2.me/submissions/b3e3847f-70db-43d0-9f7c-6f85597a21b2

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ProjKeepsLetter
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutedExponentApplyBlock
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_primed_embedding_injective
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_mem_chainSet

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
theorem _root_.solution (hch : ∀ j i, D.chain j i ⊆ D.LLj j) (j j' : Fin D.J) (hj : j ≠ j')
    (i : Fin (D.nch j)) (i' : Fin (D.nch j')) : Disjoint (D.chainSet j i) (D.chainSet j' i') := by
  rw [Finset.disjoint_left]
  intro z hz hz'
  rw [D.mem_chainSet] at hz hz'
  rcases hz with ⟨b, hb, rfl⟩ | ⟨m, rfl⟩ <;> rcases hz' with ⟨b', hb', h⟩ | ⟨m', h⟩
  · simp only [mb, Sum.inl.injEq] at h
    subst h
    have h1 := hch j i hb
    have h2 := hch j' i' hb'
    simp only [LLj, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact hj (h1.symm.trans h2)
  · simp [mw, mb] at h
  · simp [mw, mb] at h
  · simp only [mw, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq] at h
    exact hj (D.primed_embedding_injective h.1).symm
end Formalism.MainNotions.PlaneGram.TwistData
