-- Prove2me | solution 1 for FairSelling.EqualProceedsExampleThree.max_price_val
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T02:26:04.591798+00:00
-- url     : https://prove2.me/submissions/4a003e9d-42b8-45cb-8d7f-c692b3d6b082

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_EqualProceedsExamples
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.EqualProceedsExampleThree
variable (N : ℕ)


theorem solution (g : Fin (N + 1)) : max (price N g) (val N g) = 1 := by
  by_cases h : g = 0 <;> simp [price,val,h]
