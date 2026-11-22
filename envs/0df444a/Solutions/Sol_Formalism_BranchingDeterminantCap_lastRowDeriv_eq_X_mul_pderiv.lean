-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.lastRowDeriv_eq_X_mul_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:29:32.056474+00:00
-- url     : https://prove2.me/submissions/e6c6f2d8-3225-4d93-a512-732e62355e93

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_lastRowDeriv_X
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
theorem _root_.solution (R : Type*) [CommRing R] (n : ℕ) (s t : Fin n) (F : BP R n) :
    bmZ R n s t F = X (Fin.last n, s) * pderiv (Fin.last n, t) F := by
  have : bmZ R n s t = (X (Fin.last n, s) : BP R n) • (pderiv (Fin.last n, t) : Derivation R (BP R n) (BP R n)) := by
    refine MvPolynomial.derivation_ext fun v => ?_
    rw [lastRowDeriv_X, Derivation.smul_apply, pderiv_X, smul_eq_mul]
    obtain ⟨a, b⟩ := v
    by_cases h1 : b = t <;> by_cases h2 : a = Fin.last n <;> simp [h1, h2, Pi.single_apply]
  rw [this, Derivation.smul_apply, smul_eq_mul]
end Formalism.BranchingDeterminantCap
