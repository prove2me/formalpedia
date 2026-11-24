-- Prove2me | solution 1 for FairChores.cbar_eq_cost_of_ne_price
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T03:28:39.59495+00:00
-- url     : https://prove2.me/submissions/2fdd52d7-5d6a-4f3c-91c9-1e03af19d36f

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresEnvy
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
variable {ci p : T → ℝ}
omit [Fintype T] [DecidableEq T]


theorem solution {t : T} (h : cbar ci p t ≠ p t) : cbar ci p t = ci t := by
  unfold cbar at *; exact min_eq_left (le_of_not_ge fun hle => h (min_eq_right hle))
