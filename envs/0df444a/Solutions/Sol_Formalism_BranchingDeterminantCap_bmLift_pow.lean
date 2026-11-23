-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmLift_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:00.57283+00:00
-- url     : https://prove2.me/submissions/9ba6f00c-55b3-422d-a86f-d283a6a8f7de

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmLift_mul
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmLift_one
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
theorem _root_.solution {R : Type*} [CommRing R] {n : ℕ} {lam b : Fin n → ℕ}
    {f : MvPolynomial (Fin n × Fin n) R} {G : BP R n} (h : bmLift R n lam b f G) (k : ℕ) :
    bmLift R n (k • lam) (k • b) (f ^ k) (G ^ k) := by
  induction k with
  | zero => simpa using bmLift_one R n
  | succ k ih =>
    have := bmLift_mul ih h
    rw [succ_nsmul, succ_nsmul, pow_succ, pow_succ]
    exact this
end Formalism.BranchingDeterminantCap
