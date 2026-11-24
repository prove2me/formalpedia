-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.YP_preimage1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:51:12.03092+00:00
-- url     : https://prove2.me/submissions/aabf19c6-c80b-43ed-8e46-6bf0608d2f5b

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_IntegralMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SecondEmbeddingInjective
import Theorems.Thm_Formalism_MainNotions_PlaneGram_mem_initSet
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_seg_eB

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
theorem _root_.solution (m : Fin D.r) :
    (D.YPset j m).preimage (D.e1 j) (D.second_embedding_injective j).injOn = initSet (D.nB j + D.r) (D.stg j m) := by
  ext k
  simp only [Finset.mem_preimage, mem_initSet]
  induction k using Fin.addCases with
  | left a =>
    have h1 : D.e1 j (Fin.castAdd D.r a) ∈ D.YPset j m := by
      rw [second_embedding_castAdd]
      unfold YPset
      exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (by simp [LLj, seg_eB]))
    have h2 : (Fin.castAdd D.r a).val < D.stg j m := by
      simp only [Fin.coe_castAdd, stg]
      have := a.2
      omega
    exact iff_of_true h1 h2
  | right m' =>
    rw [second_embedding_natAdd]
    have hm := m.2
    have hm' := m'.2
    split_ifs with h0
    · simp only [YPset, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, mb, mlab, mtp,
      reduceCtorEq, and_false, exists_false, false_or, or_false, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq,
      exists_eq_right, Fin.coe_natAdd, stg]
      rw [Fin.val_rev] at h0
      constructor
      · intro h
        exact h.elim
      · intro h
        omega
    · simp only [YPset, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, mb, mlab, mtp,
      reduceCtorEq, and_false, exists_false, false_or, or_false, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq,
      exists_eq_right, Fin.coe_natAdd, stg]
      rw [Fin.val_rev] at h0
      rw [Fin.lt_iff_val_lt_val, Fin.val_rev]
      omega
end Formalism.MainNotions.PlaneGram.TwistData
