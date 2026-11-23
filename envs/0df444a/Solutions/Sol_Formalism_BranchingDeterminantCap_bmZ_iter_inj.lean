-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmZ_iter_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:47.377798+00:00
-- url     : https://prove2.me/submissions/25aee912-64c6-4d1e-9b00-7badacf23cfe

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_lastRowDeriv_weighted_homogeneous
import Theorems.Thm_Formalism_BranchingDeterminantCap_lastRowDeriv_injective_weighted
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
theorem _root_.solution (R : Type*) [CommRing R] [IsDomain R] [CharZero R] (n : ℕ) (j l : Fin n) (hjl : j ≠ l)
    (k : ℕ) (β : Fin n → ℤ) (F : BP R n) (hF : IsWeightedHomogeneous (zW n) F β) (hk : (k : ℤ) ≤ β l)
    (h0 : (bmZ R n j l)^[k] F = 0) : F = 0 := by
  induction k generalizing β F with
  | zero => simpa using h0
  | succ k ih =>
    rw [Function.iterate_succ_apply] at h0
    have hW := lastRowDeriv_weighted_homogeneous R n j l β F hF
    have h1 : bmZ R n j l F = 0 := by
      refine ih _ _ hW ?_ h0
      have e : (β + (Pi.single j 1 - Pi.single l 1) : Fin n → ℤ) l = β l - 1 := by
        rw [Pi.add_apply, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hjl)]
        ring
      rw [e]
      omega
    exact lastRowDeriv_injective_weighted R n j l β F hF (by omega) h1
end Formalism.BranchingDeterminantCap
