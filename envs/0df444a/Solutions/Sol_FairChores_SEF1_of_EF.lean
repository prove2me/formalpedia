-- Prove2me | solution 1 for FairChores.SEF1_of_EF
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T03:29:08.674341+00:00
-- url     : https://prove2.me/submissions/713489e1-7e57-449b-b238-35a35a194673

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresEnvy
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
variable {c : Fin n → T → ℝ} {p : T → ℝ} {o : Outcome T n}
omit [Fintype T] [DecidableEq T]


theorem solution (h : EF c p o) : SEF1 c p o := by
  intro i j; exact ⟨fun _ => h i j, fun _ => Or.inl (h i j)⟩
