-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.capDet_commute_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:40:40.008075+00:00
-- url     : https://prove2.me/submissions/6aa8e6d2-b1d6-4d81-8740-8f4d8e37a664

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap

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
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
    (E : Fin n → Fin n → Module.End R M) (u : ℤ) (x : Module.End R M) (hx : ∀ i j, Commute x (E i j)) :
    Commute x (capDet E u) := by
  unfold capDet bmPi bmM
  refine Commute.sum_right _ _ _ fun α _ => ?_
  rw [zsmul_eq_mul]
  refine ((Int.cast_commute _ x).symm).mul_right ?_
  refine Commute.list_prod_right _ _ fun y hy => ?_
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hy
  unfold bmF
  split_ifs
  · exact ((Int.cast_commute _ x).symm).sub_right (hx _ _)
  · exact (Commute.zero_right x).sub_right (hx _ _)
end Formalism.BranchingDeterminantCap
