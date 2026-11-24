-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qs_laplace_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:44:38.516395+00:00
-- url     : https://prove2.me/submissions/3c2e23db-9257-4198-b96d-cef352635694

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsMnTranspose
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsRemIffAdd
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
theorem _root_.solution (g' : Matrix (Fin n) (Fin n) R) (hg : g * g' = 1) (J K : Finset (Fin n)) (a : Fin n) :
    ∑ m, (if m ∉ K then ((qs_sg K m : ℤ) : R) * qs_mn g J (insert m K) * g' m a else 0) =
      if a ∈ J then ((qs_sg (J.erase a) a : ℤ) : R) * qs_mn g (J.erase a) K else 0 := by
  have h1 : ∀ m, (if m ∉ K then ((qs_sg K m : ℤ) : R) * qs_mn g J (insert m K) * g' m a else 0) =
      ∑ k ∈ J, ((qs_sg (J.erase k) k : ℤ) : R) * qs_mn g (J.erase k) K * (g k m * g' m a) := by
    intro m
    have := qs_laplace_col g J K m
    rw [← ite_not] at this
    calc _ = (if m ∉ K then ((qs_sg K m : ℤ) : R) * qs_mn g J (insert m K) else 0) * g' m a := by
          split_ifs <;> simp
      _ = _ := by rw [← this, Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ => by ring
  rw [Finset.sum_congr rfl (fun m _ => h1 m), Finset.sum_comm]
  have h2 : ∀ k, ∑ m, g k m * g' m a = if k = a then 1 else 0 := by
    intro k
    have := congrFun (congrFun hg k) a
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    exact this
  simp_rw [← Finset.mul_sum, h2]
  simp [Finset.sum_ite_eq']
end Formalism.InvariantFactorPaths.ColumnFamilies
