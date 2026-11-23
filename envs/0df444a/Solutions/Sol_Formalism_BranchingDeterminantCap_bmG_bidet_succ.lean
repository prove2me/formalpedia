-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmG_bidet_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:24:36.346963+00:00
-- url     : https://prove2.me/submissions/4edac7e7-c756-4bcd-a0b6-192f768a3323

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
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
theorem _root_.solution (R : Type*) [CommRing R] {r n K : ℕ} (sz : Fin (K + 1) → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin r) :
    bideterminant R sz hsz I = initMinor R (I 0) (hsz 0) *
      bideterminant R (fun k : Fin K => sz k.succ) (fun k => hsz k.succ) (fun k => I k.succ) := by
  simp only [bideterminant, Fin.prod_univ_succ]
end Formalism.BranchingDeterminantCap
