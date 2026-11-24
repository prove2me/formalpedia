-- Prove2me | solution 1 for FairSelling.PS_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T02:26:14.306581+00:00
-- url     : https://prove2.me/submissions/3deb9a04-b9ae-44c2-b778-d2f2c4f5182e

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EqualProceeds
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [DecidableEq G]


theorem solution (v p : G → ℝ) (hp : ∀ g, 0 ≤ p g) : 0 ≤ PS n v p := by
  apply div_nonneg _ (Nat.cast_nonneg n)
  exact Finset.sum_nonneg fun g _ => (hp g).trans (le_max_left _ _)
