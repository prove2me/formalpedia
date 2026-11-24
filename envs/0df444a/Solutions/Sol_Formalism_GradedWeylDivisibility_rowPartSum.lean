-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.rowPartSum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:03.640449+00:00
-- url     : https://prove2.me/submissions/d601081a-56db-450f-b946-a75c3c606115

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_RowNuSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GradedWeylDivisibility
open MvPolynomial
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution : RowNuSum := by
  classical
  intro r n ν hn k
  let g : ℕ → ℕ := fun i => if i < k then (if h : i < n then ν ⟨i, h⟩ else 0) else 0
  have hL : ∑ a : Fin r with a.val < k, rowNu (r := r) ν a = ∑ i ∈ Finset.range r, g i := by
    rw [Finset.sum_filter, ← Fin.sum_univ_eq_sum_range g r]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [g, rowNu]
  have hR : ∑ t : Fin n with t.val < k, ν t = ∑ i ∈ Finset.range n, g i := by
    rw [Finset.sum_filter, ← Fin.sum_univ_eq_sum_range g n]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [g, dif_pos t.isLt]
  rw [hL, hR]
  refine (Finset.sum_subset (fun i hi => ?_) (fun i hi hni => ?_)).symm
  · simp only [Finset.mem_range] at hi ⊢; omega
  · simp only [Finset.mem_range] at hi hni
    simp only [g, dif_neg hni, ite_self]
end Formalism.GradedWeylDivisibility
