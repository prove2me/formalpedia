-- Prove2me | solution 1 for FairSelling.SEFX_of_SEFXs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:38:28.028988+00:00
-- url     : https://prove2.me/submissions/83c1d07b-e973-4721-a794-2f4b2c004cee

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [DecidableEq G] {n : ℕ}
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}
namespace FairSelling
theorem _root_.solution (hvalid : o.Valid p) (ho : SEFXs v p o) : SEFX v p o := by
  intro i j
  refine ⟨(ho i j).1, fun hj => Or.inr fun g hg => ?_⟩
  have := (ho i j).2 g hg
  have hmi := hvalid.2.2.1 i
  rw [hj] at this
  linarith
end FairSelling
