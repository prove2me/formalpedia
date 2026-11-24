-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.Th_post
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:36:43.755967+00:00
-- url     : https://prove2.me/submissions/ea2e23bc-70b7-40da-bbbf-b9440bb4deda

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutionXFirstEmbedding
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MonomialMemPolKSg
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Th_supp
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_outSeg_of_not_segL
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_eB_surj
import Theorems.Thm_Formalism_MainNotions_PlaneGram_eOut_apply


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
open Formalism.MainNotions.PlaneGram.TwistData
variable {K : Type} [Field K] (D : TwistData K) (j : Fin D.J)
variable {ι : Type} [Fintype ι]
variable (cc : (Fin (D.nB j + D.r) × Fin D.r →₀ ℕ) → ι → K) (PP : ι → MvPolynomial (D.ML × Fin D.r) K)
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution (hPP : ∀ b, ∀ ξ ∈ (PP b).support, D.PostE j ξ ∧ ∀ i, ¬ D.SegL j i → ∀ a, ξ (i, a) = 0)
    (ζ : D.EM) (hζ : D.PreE j ζ) (ζ' : D.EM) (h : ζ' ∈ (D.Th j cc PP (monomial ζ 1)).support) :
    D.PostE j ζ' ∧ ∀ i, ¬ D.SegL j i → ∀ a, ζ' (i, a) = ζ (i, a) := by
  obtain ⟨b, ξ, hξ, rfl⟩ := D.Th_supp j cc PP ζ ζ' h
  obtain ⟨hpost, hzero⟩ := hPP b ξ hξ
  have hO : ∀ i, ¬ D.outSeg j i → ∀ a, eOut (D.outSeg j) ζ (i, a) = 0 := by
    intro i hi a
    exact (eOut_apply (out := D.outSeg j) ζ (i, a)).trans (if_neg hi)
  have hmb : ∀ c, D.seg c = j → ¬ D.outSeg j (D.mb c) := by
    intro c hc hout
    obtain ⟨a, rfl⟩ := eB_surj (D := D) (j := j) c hc
    exact hout ⟨Fin.castAdd D.r a, by rw [first_embedding_castAdd]⟩
  have hml : ∀ m, ¬ D.outSeg j (D.mlab (j, m)) := by
    intro m hout
    exact hout ⟨Fin.natAdd (D.nB j) (Fin.rev m), by rw [first_embedding_natAdd, Fin.rev_rev]⟩
  have hmt : ∀ m a, eOut (D.outSeg j) ζ (D.mtp (j, m), a) = 0 := by
    intro m a
    rw [eOut_apply]
    split_ifs
    · exact hζ.2.2 m a
    · rfl
  have hldeg : ∀ i, (∀ a, eOut (D.outSeg j) ζ (i, a) = 0) →
      ldeg (eOut (D.outSeg j) ζ + ξ) i = ldeg ξ i := by
    intro i hi
    simp only [ldeg, Finsupp.add_apply, hi, zero_add]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro c hc
    rw [hldeg _ (hO _ (hmb c hc))]
    exact hpost.1 c hc
  · intro m
    rw [hldeg _ (hO _ (hml m)), hldeg _ (hmt m)]
    exact hpost.2.1 m
  · intro m
    rw [hldeg _ (hmt m)]
    exact hpost.2.2.1 m
  · intro m hm a
    rw [Finsupp.add_apply, hmt m a, zero_add]
    exact hpost.2.2.2 m hm a
  · intro i hi a
    rw [Finsupp.add_apply, hzero i hi a, add_zero]
    exact (eOut_apply (out := D.outSeg j) ζ (i, a)).trans (if_pos (D.outSeg_of_not_segL j i hi))
end Formalism.MainNotions.PlaneGram.TwistData
