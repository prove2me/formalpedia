-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.ql_w_assoc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:44:34.953535+00:00
-- url     : https://prove2.me/submissions/769e5506-6c73-4789-ac58-eec526c7143b

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsMnTranspose
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LaplaceExpansionColumn
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_s_assoc
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_sum_w

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
theorem _root_.solution (A B C I : Finset (Fin n)) :
    ∑ M, ql_w R A B M * ql_w R M C I = ∑ M, ql_w R B C M * ql_w R A M I := by
  have h1 : ∑ M, ql_w R A B M * ql_w R M C I = wedgeSign R A B * ql_w R (A ∪ B) C I := by
    rw [← ql_sum_w A B (fun M => ql_w R M C I)]; exact sum_congr rfl fun _ _ => mul_comm _ _
  have h2 : ∑ M, ql_w R B C M * ql_w R A M I = wedgeSign R B C * ql_w R A (B ∪ C) I := by
    rw [← ql_sum_w B C (fun M => ql_w R A M I)]; exact sum_congr rfl fun _ _ => mul_comm _ _
  rw [h1, h2, ql_w, ql_w, union_assoc]
  split_ifs
  · exact ql_s_assoc A B C
  · simp
end Formalism.InvariantFactorPaths.ColumnFamilies
