-- Prove2me | solution 2 for FairSelling.epsSEF1_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:38:38.143548+00:00
-- url     : https://prove2.me/submissions/7144c47c-4adf-4b0e-b0f7-7fb017b439da

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [DecidableEq G] {n : ℕ}
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}
namespace FairSelling
theorem _root_.solution {eps eps' : ℝ} (h : eps ≤ eps') (ho : epsSEF1 v p eps o) :
    epsSEF1 v p eps' o := by
  intro i j
  refine ⟨(ho i j).1, fun hj => ?_⟩
  rcases (ho i j).2 hj with hEF | ⟨g, hg, hle⟩
  · exact Or.inl (by linarith)
  · exact Or.inr ⟨g, hg, le_trans hle (by linarith)⟩
end FairSelling
