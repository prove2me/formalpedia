-- Prove2me | solution 2 for FairChores.cbar_eq_cost_of_ne_price
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:53:25.836261+00:00
-- url     : https://prove2.me/submissions/2eb4c200-a2bb-4477-aa84-2ed2f2ee88e0

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresEnvy

set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
variable {ci p : T → ℝ}
omit [Fintype T] [DecidableEq T]
namespace FairChores
theorem _root_.solution {t : T} (h : cbar ci p t ≠ p t) : cbar ci p t = ci t := by
  rcases min_cases (ci t) (p t) with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact h1
  · exact absurd h1 h
end FairChores
