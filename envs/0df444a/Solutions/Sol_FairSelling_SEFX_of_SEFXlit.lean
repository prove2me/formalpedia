-- Prove2me | solution 1 for FairSelling.SEFX_of_SEFXlit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:36:26.521423+00:00
-- url     : https://prove2.me/submissions/d235f592-cdfc-4712-8a7f-cc14859648ff

import Mathlib
import Definitions.Def_RequestProject_Selling

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}
omit [Fintype G]
namespace FairSelling
theorem _root_.solution (hvalid : o.Valid p) (h : SEFXlit v p o) : SEFX v p o := by
  intro i j
  refine ⟨(h i j).1, fun hj => Or.inr fun g hg => ?_⟩
  have := (h i j).2 hj g hg
  have hmi := hvalid.2.2.1 i
  linarith
end FairSelling
