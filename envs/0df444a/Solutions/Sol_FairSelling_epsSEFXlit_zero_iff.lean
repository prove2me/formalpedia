-- Prove2me | solution 1 for FairSelling.epsSEFXlit_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T02:35:56.26164+00:00
-- url     : https://prove2.me/submissions/2c4f04e7-f192-43d4-86d4-18807705e843

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [DecidableEq G] {n : ℕ}
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}


theorem solution : epsSEFXlit v p 0 o ↔ SEFXlit v p o := by
  simp [epsSEFXlit,SEFXlit]
