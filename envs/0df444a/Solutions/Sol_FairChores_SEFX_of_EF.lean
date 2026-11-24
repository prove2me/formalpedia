-- Prove2me | solution 1 for FairChores.SEFX_of_EF
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:21:10.313826+00:00
-- url     : https://prove2.me/submissions/e5a5cf70-08c2-4d5c-adfd-74a46e2c16d0

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
theorem _root_.solution (h : EF c p o) : SEFX c p o := fun i j =>
  ⟨fun _ => h i j, fun _ => Or.inl (h i j)⟩
end FairChores
