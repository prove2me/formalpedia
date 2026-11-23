-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmG_initMinor_rowHom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:24:35.981982+00:00
-- url     : https://prove2.me/submissions/87c93e5b-7093-4aab-b58b-4463052fee8a

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod


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
theorem _root_.solution (R : Type*) [CommRing R] {r n s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n) :
    IsWeightedHomogeneous (rowW r n) (initMinor R (n := n) I hs) (∑ p : Fin s, Pi.single (I p) 1) := by
  unfold initMinor
  rw [Matrix.det_apply]
  refine IsWeightedHomogeneous.sum _ _ _ fun σ _ => ?_
  rw [← mem_weightedHomogeneousSubmodule]
  refine zsmul_mem ?_ _
  rw [mem_weightedHomogeneousSubmodule,
    ← Equiv.sum_comp σ (fun p => (Pi.single (I p) 1 : Fin r → ℕ))]
  refine IsWeightedHomogeneous.prod _ _ _ fun q _ => ?_
  exact isWeightedHomogeneous_X R (rowW r n) _
end Formalism.BranchingDeterminantCap
