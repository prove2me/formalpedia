-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmZ_euler
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:35:18.616625+00:00
-- url     : https://prove2.me/submissions/d40984bc-ab19-42db-a4ff-e56017007fc3

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bm_weight_zW
import Theorems.Thm_Formalism_BranchingDeterminantCap_lastRowDiagDeriv_coeff

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
theorem _root_.solution (R : Type*) [CommRing R] (n : ℕ) (β : Fin n → ℤ) (s : Fin n) (F : BP R n)
    (hF : IsWeightedHomogeneous (zW n) F β) : bmZ R n s s F = ((β s : ℤ) : R) • F := by
  ext m
  rw [lastRowDiagDeriv_coeff, coeff_smul, smul_eq_mul]
  by_cases hc : coeff m F = 0
  · rw [hc, mul_zero, mul_zero]
  · have h1 := hF hc
    have h2 := bm_weight_zW m s
    rw [h1] at h2
    rw [h2, Int.cast_natCast]
end Formalism.BranchingDeterminantCap
