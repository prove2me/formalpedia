-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.lastRowDiagDeriv_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:29:07.220815+00:00
-- url     : https://prove2.me/submissions/fab98619-793d-4271-b185-f977acef8306

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_lastRowDeriv_eq_X_mul_pderiv
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
theorem _root_.solution (R : Type*) [CommRing R] (n : ℕ) (s : Fin n) (F : BP R n)
    (m : Fin (n + 1) × Fin n →₀ ℕ) :
    coeff m (bmZ R n s s F) = (m (Fin.last n, s) : R) * coeff m F := by
  classical
  rw [lastRowDeriv_eq_X_mul_pderiv, coeff_X_mul']
  split_ifs with h
  · rw [coeff_pderiv]
    have hle : Finsupp.single (Fin.last n, s) 1 ≤ m := by
      rw [Finsupp.single_le_iff]; exact Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 h)
    rw [tsub_add_cancel_of_le hle]
    have h1 : (m - Finsupp.single (Fin.last n, s) 1 : Fin (n + 1) × Fin n →₀ ℕ) (Fin.last n, s) + 1 =
        m (Fin.last n, s) := by
      have := Finsupp.single_le_iff.1 hle
      simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]
      omega
    rw [mul_comm]
    congr 1
    have h2 := congrArg (Nat.cast : ℕ → R) h1
    push_cast at h2
    exact h2
  · rw [Finsupp.notMem_support_iff.1 h]; simp
end Formalism.BranchingDeterminantCap
