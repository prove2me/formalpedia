-- Prove2me | solution 1 for FairSelling.SEFXlit_of_SEFXs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:39:11.121807+00:00
-- url     : https://prove2.me/submissions/0ec3be29-0373-4329-840a-6f7f48edae8c

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [DecidableEq G] {n : ℕ}
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}
namespace FairSelling
theorem _root_.solution (ho : SEFXs v p o) : SEFXlit v p o := by
  intro i j
  refine ⟨(ho i j).1, fun hj g hg => ?_⟩
  have := (ho i j).2 g hg
  rw [hj] at this
  linarith
end FairSelling
