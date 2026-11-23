-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmF_low_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:23:16.123243+00:00
-- url     : https://prove2.me/submissions/30cab27a-8773-44c8-8982-ff6085ca88ff

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_low_zero
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_low_add

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
theorem _root_.solution {R : Type*} [CommRing R] {n : ℕ} {D : ℤ} {ι : Type*} (s : Finset ι) (L : ι → BP R n)
    (h : ∀ i ∈ s, IsLow D (L i)) : IsLow D (∑ i ∈ s, L i) := by
  exact Finset.sum_induction L (fun x => IsLow D x) (fun _ _ ha hb => bmF_low_add ha hb)
    (bmF_low_zero D) h
end Formalism.BranchingDeterminantCap
