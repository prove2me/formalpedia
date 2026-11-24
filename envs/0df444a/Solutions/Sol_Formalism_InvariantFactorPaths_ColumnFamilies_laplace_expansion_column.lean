-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.laplace_expansion_column
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:44:36.722481+00:00
-- url     : https://prove2.me/submissions/bfd48887-daf5-4869-a5a6-00b122aecbb5

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsMnTranspose
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LaplaceExpansionColumn
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_sr_single
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_w_single
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_laplace_col


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
variable (g : Matrix (Fin n) (Fin n) R)
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (B I : Finset (Fin n)) (m : Fin n) :
    ∑ M, ∑ k, qs_mn g M B * g k m * ql_w R M {k} I = wedgeSign R B {m} * qs_mn g I (B ∪ {m}) := by
  rw [sum_comm]
  have h1 : ∀ k, ∑ M, qs_mn g M B * g k m * ql_w R M {k} I =
      if k ∈ I then ((qs_sg (I.erase k) k : ℤ) : R) * qs_mn g (I.erase k) B * g k m else 0 := by
    intro k
    simp only [ql_w_single, mul_ite, mul_zero, sum_ite_eq', mem_univ, if_true]
    split_ifs
    · ring
    · rfl
  simp only [h1]
  rw [sum_ite_mem, univ_inter, qs_laplace_col, wedgeSign]
  by_cases hm : m ∈ B
  · rw [if_pos hm, if_neg (by simpa using hm), zero_mul]
  · rw [if_neg hm, if_pos (by simpa using hm), ql_sr_single, union_comm, ← insert_eq]
end Formalism.InvariantFactorPaths.ColumnFamilies
