-- Prove2me | solution 1 for FairSelling.epsSEFX_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:33:17.258487+00:00
-- url     : https://prove2.me/submissions/8ae15f9f-03ea-436f-b9ab-75257a91ed79

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [DecidableEq G] {n : ℕ}
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}
namespace FairSelling
theorem _root_.solution {eps eps' : ℝ} (h : eps ≤ eps') (ho : epsSEFX v p eps o) :
    epsSEFX v p eps' o := by
  intro i j
  refine ⟨(ho i j).1, fun hj => ?_⟩
  rcases (ho i j).2 hj with hEF | hall
  · exact Or.inl (by linarith)
  · exact Or.inr fun g hg => le_trans (hall g hg) (by linarith)
end FairSelling
