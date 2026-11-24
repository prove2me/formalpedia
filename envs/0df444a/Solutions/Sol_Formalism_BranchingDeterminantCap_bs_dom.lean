-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bs_dom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:36:03.82653+00:00
-- url     : https://prove2.me/submissions/c4e53a47-abf7-488e-a85b-b149849609ca

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchScale
import Theorems.Thm_Formalism_GradedWeylDivisibility_bidetDominance
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_standardMonomialSpanDomain
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
open Formalism.REAL
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution {r n : ℕ} (ν : Fin n → ℕ) (f : MvPolynomial (Fin r × Fin n) ℂ)
    (hf : f ∈ dualWeyl ℂ r n ν) : ∀ m ∈ f.support,
      (∀ k : ℕ, (∑ a : Fin r with a.val < k, rowDeg m a) ≤ ∑ t : Fin n with t.val < k, ν t) ∧
      ∑ a : Fin r, rowDeg m a = ∑ t : Fin n, ν t := by
  classical
  rw [standardMonomialSpanDomain ℂ r n ν] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, sz, hsz, I, hshape, rfl⟩ := hx
    intro m hm
    have h := bidetDominance ℂ r n K sz hsz I m hm
    rw [hshape] at h
    exact h
  | zero =>
    intro m hm
    simp at hm
  | add x y _ _ hx hy =>
    intro m hm
    rcases Finset.mem_union.mp (support_add hm) with h | h
    · exact hx m h
    · exact hy m h
  | smul c x _ hx =>
    intro m hm
    exact hx m (support_smul hm)
end Formalism.BranchingDeterminantCap
