-- Prove2me | solution 1 for FairSelling.truncSum_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:27:33.219334+00:00
-- url     : https://prove2.me/submissions/bb845197-dca6-4273-97e8-9595cf3175d4

import Mathlib
import Definitions.Def_RequestProject_Selling

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
omit [DecidableEq G]
namespace FairSelling
theorem _root_.solution (v p : G → ℝ) : Monotone (truncSum n v p) := by
  intro t t' h;
  exact div_le_div_of_nonneg_right ( Finset.sum_le_sum fun _ _ => max_le_max_left _ ( min_le_min_left _ h ) ) ( Nat.cast_nonneg _ )
end FairSelling
