-- Prove2me | solution 1 for FairSelling.SEF1_of_SEF1lit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:36:30.574533+00:00
-- url     : https://prove2.me/submissions/fc5d32af-f6a3-48a9-9cf0-252f3324ee20

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
theorem _root_.solution (hvalid : o.Valid p) (h : SEF1lit v p o) : SEF1 v p o := by
  intro i j
  refine ⟨(h i j).1, fun hj => Or.inr ?_⟩
  obtain ⟨g, hg, hx⟩ := (h i j).2 hj
  have hmi := hvalid.2.2.1 i
  exact ⟨g, hg, by linarith⟩
end FairSelling
