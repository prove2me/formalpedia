-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.dualWeylModuleDominanceOfSpan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:58:48.71504+00:00
-- url     : https://prove2.me/submissions/f8cd81fa-27c9-4452-8cd2-88b3c4428887

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_BideterminantDominance
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylDominanceOf
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowNu_partial_sum
import Theorems.Thm_Formalism_GradedWeylDivisibility_bideterminantDominance


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution : DualWeylDominanceOf := by
  intro hspan r n ν hnr hν f hf
  rw [hspan r n ν hν] at hf
  have htot : ∑ a : Fin r, rowNu (r := r) ν a = ∑ t : Fin n, ν t := by
    have h := rowNu_partial_sum ν hnr r
    first
      | rwa [Finset.filter_true_of_mem (fun (a : Fin r) _ => a.isLt),
          Finset.filter_true_of_mem (fun (t : Fin n) _ => lt_of_lt_of_le t.isLt hnr)] at h
      | (have e1 : (Finset.univ.filter fun a : Fin r => a.val < r) = Finset.univ := by
            ext a; simp [a.isLt]
         have e2 : (Finset.univ.filter fun t : Fin n => t.val < r) = Finset.univ := by
            ext t; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]; omega
         rw [e1, e2] at h
         exact h)
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨K, sz, hsz, I, hshape, rfl⟩ := hg
    intro m hm
    obtain ⟨hpre, htot'⟩ := bideterminantDominance ℤ r n K sz hsz I m hm
    refine ⟨fun k => ?_, ?_⟩
    · rw [rowNu_partial_sum _ hnr k, ← hshape]
      exact hpre k
    · rw [htot, ← hshape]
      exact htot'
  | zero =>
    intro m hm
    simp at hm
  | add x y _ _ hx hy =>
    intro m hm
    rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h | h
    · exact hx m h
    · exact hy m h
  | smul c x _ hx =>
    intro m hm
    first
      | exact hx m (MvPolynomial.support_smul hm)
      | (apply hx m
         rw [MvPolynomial.mem_support_iff] at hm ⊢
         intro h0
         apply hm
         simp [h0])
end Formalism.GradedWeylDivisibility
