-- Prove2me | solution 2 for FairChores.SEF1_of_EF
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:52:58.232015+00:00
-- url     : https://prove2.me/submissions/0bdde2c7-ba07-48b7-b39c-76c5e73b3e52

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresEnvy

set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
variable {c : Fin n → T → ℝ} {p : T → ℝ} {o : Outcome T n}
omit [Fintype T] [DecidableEq T]
namespace FairChores
theorem _root_.solution (h : EF c p o) : SEF1 c p o := fun i j =>
  ⟨fun _ => h i j, fun _ => Or.inl (h i j)⟩
end FairChores
