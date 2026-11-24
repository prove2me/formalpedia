-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.ql_s_assoc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:04.7869+00:00
-- url     : https://prove2.me/submissions/61f9eb31-191e-4cfd-a5b6-e90b8ebaf6ed

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsMnTranspose
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LaplaceExpansionColumn
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_sr_union_left
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_sr_union_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
variable {R : Type*} [CommRing R]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (A B C : Finset (Fin n)) :
    wedgeSign R A B * wedgeSign R (A ∪ B) C = wedgeSign R B C * wedgeSign R A (B ∪ C) := by
  unfold wedgeSign
  by_cases hAB : Disjoint A B <;> by_cases hAC : Disjoint A C <;> by_cases hBC : Disjoint B C <;>
    simp only [disjoint_union_left, disjoint_union_right, hAB, hAC, hBC, if_true, if_false, and_true,
      and_false, and_self, mul_zero, zero_mul]
  rw [ql_sr_union_left hAB, ql_sr_union_right _ hBC]; ring
end Formalism.InvariantFactorPaths.ColumnFamilies
