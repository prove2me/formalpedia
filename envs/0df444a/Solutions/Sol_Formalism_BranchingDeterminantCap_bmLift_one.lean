-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmLift_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:03:01.473379+00:00
-- url     : https://prove2.me/submissions/0e3a80c3-0dc2-44cf-9d9e-969bd1c7a70a

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_low_zero
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
theorem _root_.solution (R : Type*) [CommRing R] (n : ℕ) : bmLift R n 0 0 1 1 := by
  refine ⟨Submodule.mem_inf.mpr ⟨?_, ?_⟩, ?_, ?_⟩
  · apply isWeightedHomogeneous_one
  · simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    intro l j _
    simp
  · simp only [Pi.zero_apply, Finset.sum_const_zero]
    apply isWeightedHomogeneous_one
  · have e : (1 : BP R n) - zmon R n 0 * emb R n 1 = 0 := by
      simp [zmon]
    rw [e]
    exact bmF_low_zero _
end Formalism.BranchingDeterminantCap
