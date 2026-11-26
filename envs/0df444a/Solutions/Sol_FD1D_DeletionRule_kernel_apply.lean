-- Prove2me | solution 1 for FD1D.DeletionRule.kernel_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:38:37.236329+00:00
-- url     : https://prove2.me/submissions/eecddffe-5b2e-40df-949c-e447e52fbb8b

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Markov

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators Topology
open Filter Matrix
open FD1D.DeletionRule
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {m : ℕ}
namespace FD1D.DeletionRule
theorem _root_.solution (R : DeletionRule ι m) (x y : InventoryState ι m) :
    R.kernel x y =
      ∑ d, ∑ a, if InventoryState.move x d a = y then
        R.prob x d * (1 / Fintype.card ι : ℝ) else 0 :=
  rfl
end FD1D.DeletionRule
