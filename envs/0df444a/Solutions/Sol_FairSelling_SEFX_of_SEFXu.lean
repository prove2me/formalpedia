-- Prove2me | solution 1 for FairSelling.SEFX_of_SEFXu
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:38:17.195597+00:00
-- url     : https://prove2.me/submissions/75f8b180-51ce-4263-818b-7136e1a07539

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [DecidableEq G] {n : ℕ}
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}
namespace FairSelling
theorem _root_.solution (ho : SEFXu v p o) : SEFX v p o := by
  intro i j
  refine ⟨(ho i j).1, fun hj => Or.inr fun g hg => ?_⟩
  have := (ho i j).2 g hg
  rw [hj] at this
  linarith
end FairSelling
