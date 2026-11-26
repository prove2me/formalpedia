-- Prove2me | solution 1 for FD1D.DeletionRule.kernel_move_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:44:54.734058+00:00
-- url     : https://prove2.me/submissions/5ff4f146-eaeb-4416-88b1-f3f3c6c2fc67

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Markov
import Theorems.Thm_FD1D_DeletionRule_kernel_apply
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const


attribute [local simp] FD1D.DeletionRule.kernel_apply

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators Topology
open Filter Matrix
open FD1D.DeletionRule
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {m : ℕ}
namespace FD1D.DeletionRule
theorem _root_.solution (R : DeletionRule ι m)
    (x : InventoryState ι m) {d a : ι} (hd : 0 < x.1 d) :
    0 < R.kernel x (InventoryState.move x d a) := by
  classical
  let c : ℝ := 1 / Fintype.card ι
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hterm : 0 < R.prob x d * c := mul_pos (R.occupied_pos x d hd) hc
  rw [kernel_apply]
  have hinner :
      R.prob x d * c ≤
        ∑ a', if InventoryState.move x d a' = InventoryState.move x d a
          then R.prob x d * c else 0 := by
    calc
      R.prob x d * c =
          (if InventoryState.move x d a = InventoryState.move x d a
            then R.prob x d * c else 0) := by simp
      _ ≤ ∑ a', if InventoryState.move x d a' = InventoryState.move x d a
            then R.prob x d * c else 0 :=
        Finset.single_le_sum
          (f := fun a' => if InventoryState.move x d a' = InventoryState.move x d a
            then R.prob x d * c else 0)
          (fun a' _ => by
            split_ifs
            · exact mul_nonneg (R.nonneg x d) hc.le
            · exact le_rfl)
          (Finset.mem_univ a)
  calc
    0 < R.prob x d * c := hterm
    _ ≤ ∑ a', if InventoryState.move x d a' = InventoryState.move x d a
          then R.prob x d * c else 0 := hinner
    _ ≤ ∑ d', ∑ a', if InventoryState.move x d' a' = InventoryState.move x d a
          then R.prob x d' * c else 0 := by
      exact Finset.single_le_sum
        (f := fun d' => ∑ a', if
          InventoryState.move x d' a' = InventoryState.move x d a
            then R.prob x d' * c else 0)
        (fun d' _ => Finset.sum_nonneg fun a' _ => by
          split_ifs
          · exact mul_nonneg (R.nonneg x d') hc.le
          · exact le_rfl)
        (Finset.mem_univ d)
end FD1D.DeletionRule
