-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.chainSet_Yset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:51:21.129248+00:00
-- url     : https://prove2.me/submissions/f050749a-f16b-4fa6-99c0-1e241936478f

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ProjKeepsLetter
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutedExponentApplyBlock
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_primed_embedding_injective
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_mem_chainSet
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_mem_Yset

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
theorem _root_.solution (hch : ∀ j i, D.chain j i ⊆ D.LLj j) (j : Fin D.J) (i : Fin (D.nch j))
    (j' : Fin D.J) (m : Fin D.r) :
    D.chainSet j i ⊆ D.Yset j' m ∨ Disjoint (D.chainSet j i) (D.Yset j' m) := by
  by_cases hj : j = j'
  · subst hj
    left
    intro z hz
    rw [D.mem_chainSet] at hz
    rw [D.mem_Yset]
    rcases hz with ⟨b, hb, rfl⟩ | ⟨m', rfl⟩
    · right; left
      exact ⟨b, hch j i hb, rfl⟩
    · left
      exact ⟨m', rfl⟩
  · right
    rw [Finset.disjoint_left]
    intro z hz hz'
    rw [D.mem_chainSet] at hz
    rw [D.mem_Yset] at hz'
    rcases hz with ⟨b, hb, rfl⟩ | ⟨m1, rfl⟩ <;>
      rcases hz' with ⟨m2, h⟩ | ⟨b2, hb2, h⟩ | ⟨m2, _, h⟩
    · simp [mw, mb] at h
    · simp only [mb, Sum.inl.injEq] at h
      subst h
      have h1 := hch j i hb
      simp only [LLj, Finset.mem_filter, Finset.mem_univ, true_and] at h1 hb2
      exact hj (h1.symm.trans hb2)
    · simp [mtp, mb] at h
    · simp only [mw, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq] at h
      exact hj (D.primed_embedding_injective h.1).symm
    · simp [mw, mb] at h
    · simp [mtp, mw] at h
end Formalism.MainNotions.PlaneGram.TwistData
