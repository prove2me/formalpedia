-- Prove2me | solution 2 for FairSelling.EqualProceedsExampleThree.max_price_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:30:29.210161+00:00
-- url     : https://prove2.me/submissions/5510ebb9-b6d3-4602-a0e4-4b9999264ace

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_EqualProceedsExamples

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.EqualProceedsExampleThree
variable (N : ℕ)
namespace FairSelling.EqualProceedsExampleThree
theorem _root_.solution (g : Fin (N + 1)) : max (price N g) (val N g) = 1 := by
  unfold price val; split <;> norm_num
end FairSelling.EqualProceedsExampleThree
