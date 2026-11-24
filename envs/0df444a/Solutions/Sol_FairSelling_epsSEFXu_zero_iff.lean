-- Prove2me | solution 1 for FairSelling.epsSEFXu_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:38:59.671801+00:00
-- url     : https://prove2.me/submissions/3eb1069f-5108-4241-a2b5-61b8a1d44f1a

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [DecidableEq G] {n : ℕ}
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}
namespace FairSelling
theorem _root_.solution : epsSEFXu v p 0 o ↔ SEFXu v p o := by
  unfold epsSEFXu SEFXu
  simp
end FairSelling
