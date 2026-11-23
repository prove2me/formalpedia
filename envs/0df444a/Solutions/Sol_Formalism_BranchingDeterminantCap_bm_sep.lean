-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bm_sep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:35:32.515167+00:00
-- url     : https://prove2.me/submissions/4b31013e-b2ee-4a39-b4fd-7e835d45816e

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmH_disj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution {n : ℕ} (lam : Fin n → ℕ) (d : ℕ) (β β' : Fin n → ℤ) (h : bmAdm lam d β) (h' : bmAdm lam d β')
    (hne : β ≠ β') : ∃ u, bmChi lam β u ≠ bmChi lam β' u := by
  obtain ⟨i, hi⟩ : ∃ i, β i ≠ β' i := by
    by_contra hc
    exact hne (funext fun i => by by_contra h''; exact hc ⟨i, h''⟩)
  refine ⟨((lam i : ℤ) - β' i) - ((i : ℕ) : ℤ), ?_⟩
  have h0 : bmChi lam β' (((lam i : ℤ) - β' i) - ((i : ℕ) : ℤ)) = 0 := by
    unfold bmChi
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    ring
  rw [h0]
  unfold bmChi
  rw [Finset.prod_ne_zero_iff]
  intro j _
  by_cases hij : i = j
  · subst hij
    intro hc
    apply hi
    linarith
  · have := bmH_disj (lamZ lam) (fun i => (lam i : ℤ) - β i) (fun i => (lam i : ℤ) - β' i) h.2.2 h'.2.2 i j hij
    intro hc
    apply this
    linarith
end Formalism.BranchingDeterminantCap
