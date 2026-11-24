-- Prove2me | solution 1 for FairSelling.epsSEFXs_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:39:07.989304+00:00
-- url     : https://prove2.me/submissions/d790e86c-9a56-48bb-8313-6059d96a7001

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [DecidableEq G] {n : ℕ}
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}
namespace FairSelling
theorem _root_.solution : epsSEFXs v p 0 o ↔ SEFXs v p o := by
  unfold epsSEFXs SEFXs
  simp
end FairSelling
