-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.lastRowDeriv_injective_weighted
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:38:15.301654+00:00
-- url     : https://prove2.me/submissions/f32b82c3-720c-47db-9de7-8b635c8c2bea

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_lastRowDeriv_eq_X_mul_pderiv
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmZ_euler

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
theorem _root_.solution (R : Type*) [CommRing R] [IsDomain R] [CharZero R] (n : ℕ) (j l : Fin n)
    (β : Fin n → ℤ) (F : BP R n) (hF : IsWeightedHomogeneous (zW n) F β) (hk : 1 ≤ β l)
    (h0 : bmZ R n j l F = 0) : F = 0 := by
  have h1 : pderiv (Fin.last n, l) F = 0 := by
    rw [lastRowDeriv_eq_X_mul_pderiv] at h0
    exact (mul_eq_zero.mp h0).resolve_left (X_ne_zero _)
  have h2 := bmZ_euler R n β l F hF
  rw [lastRowDeriv_eq_X_mul_pderiv, h1, mul_zero] at h2
  have hne : ((β l : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show β l ≠ 0 by omega)
  exact (smul_eq_zero.mp h2.symm).resolve_left hne
end Formalism.BranchingDeterminantCap
