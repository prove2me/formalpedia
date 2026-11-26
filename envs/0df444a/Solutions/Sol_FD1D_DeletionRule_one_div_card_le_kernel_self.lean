-- Prove2me | solution 1 for FD1D.DeletionRule.one_div_card_le_kernel_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:40:18.606581+00:00
-- url     : https://prove2.me/submissions/b1733edb-508c-4cfa-be46-b9460e00bfcf

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
    (x : InventoryState ι m) :
    (1 / Fintype.card ι : ℝ) ≤ R.kernel x x := by
  classical
  let c : ℝ := 1 / Fintype.card ι
  have hc : 0 ≤ c := by
    dsimp [c]
    positivity
  rw [kernel_apply]
  calc
    c = ∑ d, R.prob x d * c := by
      rw [← Finset.sum_mul, R.sum_prob]
      simp
    _ ≤ ∑ d, ∑ a, if InventoryState.move x d a = x
          then R.prob x d * c else 0 := by
      apply Finset.sum_le_sum
      intro d _
      calc
        R.prob x d * c ≤
            (if InventoryState.move x d d = x then R.prob x d * c else 0) := by
          simp
        _ ≤ ∑ a, if InventoryState.move x d a = x
              then R.prob x d * c else 0 := by
          exact Finset.single_le_sum
            (f := fun a => if InventoryState.move x d a = x
              then R.prob x d * c else 0)
            (fun a _ => by
              split_ifs
              · exact mul_nonneg (R.nonneg x d) hc
              · exact le_rfl)
            (Finset.mem_univ d)
end FD1D.DeletionRule
