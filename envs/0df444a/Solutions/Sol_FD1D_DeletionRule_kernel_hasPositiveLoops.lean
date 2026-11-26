-- Prove2me | solution 1 for FD1D.DeletionRule.kernel_hasPositiveLoops
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:44:58.516077+00:00
-- url     : https://prove2.me/submissions/63443b64-b791-4639-a2f2-02fcdea9497f

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Markov
import Theorems.Thm_FD1D_DeletionRule_one_div_card_le_kernel_self

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators Topology
open Filter Matrix
open FD1D.DeletionRule
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {m : ℕ}
namespace FD1D.DeletionRule
theorem _root_.solution (R : DeletionRule ι m) :
    R.kernel.HasPositiveLoops := by
  intro x
  exact lt_of_lt_of_le (by positivity : (0 : ℝ) < 1 / Fintype.card ι)
    (R.one_div_card_le_kernel_self x)
end FD1D.DeletionRule
