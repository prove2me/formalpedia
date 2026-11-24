-- Prove2me | solution 1 for FairSelling.epsSEF1_mono
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T02:36:29.770783+00:00
-- url     : https://prove2.me/submissions/5cd5fba6-b796-4cb4-b2e2-9ee01ec6f11f

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [DecidableEq G] {n : ℕ}
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}


theorem solution {eps eps' : ℝ} (h : eps ≤ eps') (ho : epsSEF1 v p eps o) :
    epsSEF1 v p eps' o := by
  intro i j; obtain ⟨hi,hj⟩ := ho i j; refine ⟨hi,?_⟩
  intro hz; rcases hj hz with hc | ⟨g,hg,hc⟩
  · left; linarith
  · right; exact ⟨g,hg,by linarith⟩
