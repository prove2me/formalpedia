-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.PsiP_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:55:25.890068+00:00
-- url     : https://prove2.me/submissions/09cdd3e2-acf6-4bf3-91dc-4e9e345b0ace

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SecondEmbeddingInjective
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SecondEmbeddingTangentIndex
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_cnt_mb
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_cnt_lab_add_tp
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_cnt_tp_zero
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_cnt_tp_le
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_cnt_not_segL
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_PsiP_HomD
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_dLL_eq_sum
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_eB_surj


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
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution {nc : ℕ} (col : Fin nc → MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K)
    (occ : Fin nc → Finset (Fin (D.nB j + D.r)))
    (hcol : ∀ k, col k ∈ PolK K D.r (fun i => if i ∈ occ k then 1 else 0))
    (hcount : ∀ i, (univ.filter fun k => i ∈ occ k).card = D.dO (D.eA j i))
    (ξ : D.EM) (hξ : ξ ∈ (D.PsiP j col occ).support) :
    D.PostE j ξ ∧ ∀ i, ¬ D.SegL j i → ∀ a, ξ (i, a) = 0 := by
  have hd := D.PsiP_HomD j col occ hcol ξ hξ
  have hc : ∀ i, (∑ k, if i ∈ occ k then 1 else 0) = D.dO (D.eA j i) := by
    intro i; rw [← hcount i, Finset.card_filter]
  have hz : ∀ i, ldeg ξ i = 0 → ∀ a, ξ (i, a) = 0 := by
    intro i h a
    unfold ldeg at h
    exact (Finset.sum_eq_zero_iff.mp h) a (Finset.mem_univ a)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro b hb
    obtain ⟨a, rfl⟩ := D.eB_surj j b hb
    rw [hd]
    simp only [cnt_mb]
    rw [hc, eA_castAdd]; rfl
  · intro m
    rw [hd, hd, ← Finset.sum_add_distrib]
    simp only [cnt_lab_add_tp]
    rw [hc, eA_natAdd, Fin.rev_rev]; rfl
  · intro m
    rw [hd]
    refine le_trans (Finset.sum_le_sum fun k _ => D.cnt_tp_le j (occ k) m) ?_
    rw [Finset.sum_comm, dLL_eq_sum]
    refine le_of_eq (Finset.sum_congr rfl fun a _ => ?_)
    rw [hc, eA_castAdd]; rfl
  · intro m h0
    apply hz
    rw [hd]
    exact Finset.sum_eq_zero fun k _ => D.cnt_tp_zero j _ m h0
  · intro i hi
    apply hz
    rw [hd]
    exact Finset.sum_eq_zero fun k _ => D.cnt_not_segL j _ i hi
end Formalism.MainNotions.PlaneGram.TwistData
