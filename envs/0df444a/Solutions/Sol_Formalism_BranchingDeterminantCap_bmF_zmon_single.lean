-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmF_zmon_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:24:22.746703+00:00
-- url     : https://prove2.me/submissions/bc79c8f6-90d3-4440-9d80-9c89946edd91

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
theorem _root_.solution (R : Type*) [CommRing R] (n : ℕ) (t : Fin n) :
    zmon R n (Pi.single t 1) = X (Fin.last n, t) := by
  unfold zmon
  rw [Finset.prod_eq_single t (fun b _ hb => by simp [Pi.single_apply, hb])
    (fun h => absurd (Finset.mem_univ t) h)]
  simp
end Formalism.BranchingDeterminantCap
