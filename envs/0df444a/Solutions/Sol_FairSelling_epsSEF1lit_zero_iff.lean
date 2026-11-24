-- Prove2me | solution 1 for FairSelling.epsSEF1lit_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T02:36:06.184296+00:00
-- url     : https://prove2.me/submissions/dc03d9c9-1bff-4f32-9389-c79b6af1b701

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [DecidableEq G] {n : ℕ}
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}


theorem solution : epsSEF1lit v p 0 o ↔ SEF1lit v p o := by
  simp [epsSEF1lit,SEF1lit]
