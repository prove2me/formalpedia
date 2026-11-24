-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.BsForm.rad_rowDiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:56.965542+00:00
-- url     : https://prove2.me/submissions/ee1f3575-0469-432e-857b-d708fa486911

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchScale
import Theorems.Thm_Formalism_BranchingDeterminantCap_BsForm_suml
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylRowStable
import Theorems.Thm_Formalism_GradedWeylDivisibility_lfockq_eval_C
import Theorems.Thm_Formalism_GradedWeylDivisibility_lfockq_eval_rowGen
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
open Formalism.REAL
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
open Formalism.BranchingDeterminantCap.BsForm
variable {n : ℕ} {sg : Fin n → ℕ}
  {D : MvPolynomial (Fin n × Fin n) ℂ → MvPolynomial (Fin n × Fin n) ℂ → ℂ}
namespace Formalism.BranchingDeterminantCap.BsForm
theorem _root_.solution (H : BsForm sg D) (p : MvPolynomial (Fin n × Fin n) ℂ) (hp : p ∈ dualWeyl ℂ n n sg)
    (h0 : ∀ q ∈ dualWeyl ℂ n n sg, D p q = 0) (a b : Fin n) (k : ℕ) :
    ∀ q ∈ dualWeyl ℂ n n sg, D (rowDiv ℂ a b k p) q = 0 := by
  intro q hq
  set N := (rowGen ℂ a b p).natDegree + k + 1 with hN
  have h1 : (rowGen ℂ a b p).natDegree < N := by omega
  have hk : k ∈ Finset.range N := Finset.mem_range.mpr (by omega)
  set P : Polynomial ℂ := ∑ i ∈ Finset.range N, Polynomial.monomial i (D (rowDiv ℂ a b i p) q) with hP
  have hP0 : P = 0 := by
    apply Polynomial.funext
    intro c
    simp only [hP, Polynomial.eval_finsetSum, Polynomial.eval_monomial, Polynomial.eval_zero]
    have e := H.adj (lfockq_mat a b c) p hp q hq
    rw [h0 _ (dualWeylRowStable ℂ n n sg _ q hq), ← lfockq_eval_rowGen, lfockq_eval_C _ N h1,
      H.suml] at e
    rw [← e]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← smul_eq_C_mul, H.smull, mul_comm]
    rfl
  have := congrArg (fun p => Polynomial.coeff p k) hP0
  simp only [hP, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Finset.sum_ite_eq',
    if_pos hk, Polynomial.coeff_zero] at this
  exact this
end Formalism.BranchingDeterminantCap.BsForm
