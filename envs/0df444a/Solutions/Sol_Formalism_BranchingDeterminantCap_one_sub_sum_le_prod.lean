-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.one_sub_sum_le_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:29:15.16997+00:00
-- url     : https://prove2.me/submissions/ce3aaa82-2749-44e1-af3d-63bff12bd6f9

import Definitions.Def_Formalism_BranchSandwichDivisors_NormLog
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Interlace
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Numeric

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution {ι : Type} (s : Finset ι) (x : ι → ℝ) (h0 : ∀ i ∈ s, 0 ≤ x i)
    (h1 : ∀ i ∈ s, x i ≤ 1) : 1 - ∑ i ∈ s, x i ≤ ∏ i ∈ s, (1 - x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have h0' : ∀ i ∈ s, 0 ≤ x i := fun i hi => h0 i (Finset.mem_insert_of_mem hi)
    have h1' : ∀ i ∈ s, x i ≤ 1 := fun i hi => h1 i (Finset.mem_insert_of_mem hi)
    have ih' := ih h0' h1'
    have hxa0 : 0 ≤ x a := h0 a (Finset.mem_insert_self a s)
    have hxa1 : x a ≤ 1 := h1 a (Finset.mem_insert_self a s)
    have hS : 0 ≤ ∑ i ∈ s, x i := Finset.sum_nonneg h0'
    nlinarith [mul_le_mul_of_nonneg_left ih' (sub_nonneg.2 hxa1), mul_nonneg hxa0 hS]
end Formalism.BranchingDeterminantCap
