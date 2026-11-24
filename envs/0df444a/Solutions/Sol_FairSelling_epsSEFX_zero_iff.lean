-- Prove2me | solution 1 for FairSelling.epsSEFX_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:52:40.006418+00:00
-- url     : https://prove2.me/submissions/61f34478-b19f-4fb4-bd2b-e1e87ac86742

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [DecidableEq G] {n : ℕ}
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}
namespace FairSelling
theorem _root_.solution : epsSEFX v p 0 o ↔ SEFX v p o := by
  unfold epsSEFX SEFX
  simp
end FairSelling
