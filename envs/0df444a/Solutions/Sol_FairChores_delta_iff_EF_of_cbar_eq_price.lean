-- Prove2me | solution 1 for FairChores.delta_iff_EF_of_cbar_eq_price
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T03:28:29.859594+00:00
-- url     : https://prove2.me/submissions/287140ae-677d-4270-824a-a482e5dd690b

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresEnvy
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
variable {ci p : T → ℝ}
omit [Fintype T] [DecidableEq T]


theorem solution {Bi Bj : Finset T} {t : T} (h : cbar ci p t = p t) :
    (p t - cbar ci p t ≥ cbarSum ci p Bi - cbarSum ci p Bj) ↔
      cbarSum ci p Bi ≤ cbarSum ci p Bj := by
  rw [h]; constructor <;> intro H <;> linarith
