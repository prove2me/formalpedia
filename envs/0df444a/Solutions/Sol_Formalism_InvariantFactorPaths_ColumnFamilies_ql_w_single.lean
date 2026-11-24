-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.ql_w_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:35:05.941603+00:00
-- url     : https://prove2.me/submissions/157b89e4-412b-4eaf-85bf-48ee85b1dc47

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsMnTranspose
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LaplaceExpansionColumn
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_sr_single

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
theorem _root_.solution (M I : Finset (Fin n)) (k : Fin n) :
    ql_w R M {k} I = if M = I.erase k then (if k ∈ I then ((qs_sg (I.erase k) k : ℤ) : R) else 0) else 0 := by
  by_cases hM : M = I.erase k
  · subst hM
    rw [if_pos rfl]
    by_cases hk : k ∈ I
    · have : I.erase k ∪ {k} = I := by
        rw [union_comm, ← insert_eq, insert_erase hk]
      rw [if_pos hk, ql_w, if_pos this, wedgeSign, if_pos (by simp), ql_sr_single]
    · rw [if_neg hk, ql_w, if_neg]
      intro h; exact hk (h ▸ mem_union_right _ (mem_singleton_self k))
  · rw [if_neg hM, ql_w]
    split_ifs with h
    · rw [wedgeSign, if_neg]
      intro hd
      apply hM
      rw [← h, union_comm, ← insert_eq, erase_insert (by simpa using hd)]
    · rfl
end Formalism.InvariantFactorPaths.ColumnFamilies
