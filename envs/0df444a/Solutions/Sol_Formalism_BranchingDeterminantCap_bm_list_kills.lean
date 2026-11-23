-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bm_list_kills
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:35:32.251616+00:00
-- url     : https://prove2.me/submissions/37c5946a-37c5-405c-a39f-d8bcfde2f500

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bm_IL_of
import Theorems.Thm_Formalism_BranchingDeterminantCap_memBranchRangeOfDefectEq
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution {n : ℕ} (lam sg : Fin n → ℕ) (hI : Interlace (lamZ lam) (fun i => (sg i : ℤ)))
    (β : Fin n → ℤ) (h : bmAdm lam (∑ s, (lam s - sg s)) β) (hne : β ≠ fun s => ((lam s - sg s : ℕ) : ℤ)) :
    ∃ u ∈ bmList lam sg, bmChi lam β u = 0 := by
  have hIL := bm_IL_of lam sg hI
  have hcast : ∀ s, ((lam s - sg s : ℕ) : ℤ) = (lam s : ℤ) - (sg s : ℤ) := fun s =>
    Nat.cast_sub (hIL s).1
  obtain ⟨i, hi⟩ : ∃ i, β i ≠ ((lam i - sg i : ℕ) : ℤ) := by
    by_contra hc
    exact hne (funext fun i => by by_contra h''; exact hc ⟨i, h''⟩)
  refine ⟨((lam i : ℤ) - β i) - ((i : ℕ) : ℤ), ?_, ?_⟩
  · unfold bmList
    rw [List.mem_flatMap]
    refine ⟨i, Finset.mem_toList.2 (Finset.mem_univ i), ?_⟩
    rw [List.mem_map]
    refine ⟨(lam i : ℤ) - β i, ?_, rfl⟩
    rw [Finset.mem_toList, Finset.mem_erase]
    constructor
    · intro hc
      apply hi
      rw [hcast]
      linarith
    · refine memBranchRangeOfDefectEq n (lamZ lam) (fun i => (sg i : ℤ)) (fun i => (lam i : ℤ) - β i) hI h.2.2 ?_ i
      unfold d0
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, h.2.1]
      push_cast
      simp only [hcast]
      rw [Finset.sum_sub_distrib]
      ring
  · unfold bmChi
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    ring
end Formalism.BranchingDeterminantCap
