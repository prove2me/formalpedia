-- Prove2me | solution 2 for FairSelling.PS_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:29:31.905457+00:00
-- url     : https://prove2.me/submissions/a927211c-0493-4296-842d-07f442a19771

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EqualProceeds

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [DecidableEq G]
namespace FairSelling
theorem _root_.solution (v p : G → ℝ) (hp : ∀ g, 0 ≤ p g) : 0 ≤ PS n v p :=
  div_nonneg (Finset.sum_nonneg fun g _ => le_trans (hp g) (le_max_left _ _))
    (Nat.cast_nonneg _)
end FairSelling
