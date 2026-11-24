-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.ql_lap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:50:46.030511+00:00
-- url     : https://prove2.me/submissions/5ec33832-afed-4253-92f3-c59b390038d3

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsMnTranspose
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LaplaceExpansionColumn
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_s_assoc
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_w_assoc
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_sum_four_comm_form
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_laplace_expansion_column
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_mn_empty
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_s_empty
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_s_max

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
theorem _root_.solution (A K I : Finset (Fin n)) :
    ∑ A', ∑ K', qs_mn g A' A * qs_mn g K' K * ql_w R A' K' I = wedgeSign R A K * qs_mn g I (A ∪ K) := by
  induction K using Finset.induction_on_max generalizing I with
  | empty =>
    simp only [ql_mn_empty, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, sum_ite_eq', mem_univ, if_true,
      ql_s_empty, one_mul, union_empty]
    simp [ql_w, ql_s_empty]
  | insert m K0 hmax ih =>
    have e1 : ∀ K', qs_mn g K' (insert m K0) = ∑ M, ∑ k, qs_mn g M K0 * g k m * ql_w R M {k} K' := by
      intro K'; rw [laplace_expansion_column, ql_s_max hmax, one_mul, union_comm, ← insert_eq]
    have h1 : ∀ A', ∑ K', qs_mn g A' A * qs_mn g K' (insert m K0) * ql_w R A' K' I =
        ∑ M, ∑ k, qs_mn g A' A * qs_mn g M K0 * g k m * ∑ K', ql_w R M {k} K' * ql_w R A' K' I := by
      intro A'
      simp only [e1, mul_sum, sum_mul]
      rw [sum_comm]; refine sum_congr rfl fun M _ => ?_
      rw [sum_comm]; exact sum_congr rfl fun k _ => sum_congr rfl fun K' _ => by ring
    have h2 : ∑ M', ∑ k, (∑ A', ∑ M, qs_mn g A' A * qs_mn g M K0 * ql_w R A' M M') * g k m * ql_w R M' {k} I =
        ∑ A', ∑ M, ∑ k, qs_mn g A' A * qs_mn g M K0 * g k m * ∑ M', ql_w R A' M M' * ql_w R M' {k} I := by
      simp only [mul_sum, sum_mul]
      rw [sum_four_comm_form]
      exact sum_congr rfl fun A' _ => sum_congr rfl fun M _ => sum_congr rfl fun k _ =>
        sum_congr rfl fun M' _ => by ring
    calc ∑ A', ∑ K', qs_mn g A' A * qs_mn g K' (insert m K0) * ql_w R A' K' I
        = ∑ A', ∑ M, ∑ k, qs_mn g A' A * qs_mn g M K0 * g k m * ∑ K', ql_w R M {k} K' * ql_w R A' K' I :=
          sum_congr rfl fun A' _ => h1 A'
      _ = ∑ A', ∑ M, ∑ k, qs_mn g A' A * qs_mn g M K0 * g k m * ∑ M', ql_w R A' M M' * ql_w R M' {k} I :=
          sum_congr rfl fun A' _ => sum_congr rfl fun M _ => sum_congr rfl fun k _ => by rw [ql_w_assoc]
      _ = ∑ M', ∑ k, (wedgeSign R A K0 * qs_mn g M' (A ∪ K0)) * g k m * ql_w R M' {k} I := by
          rw [← h2]; simp only [ih]
      _ = wedgeSign R A K0 * ∑ M', ∑ k, qs_mn g M' (A ∪ K0) * g k m * ql_w R M' {k} I := by
          simp only [mul_sum, mul_assoc]
      _ = wedgeSign R A (insert m K0) * qs_mn g I (A ∪ insert m K0) := by
          rw [laplace_expansion_column, ← mul_assoc, ql_s_assoc, ql_s_max hmax, one_mul, union_assoc, union_comm K0, ← insert_eq]
end Formalism.InvariantFactorPaths.ColumnFamilies
