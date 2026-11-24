-- Prove2me | solution 1 for FairChores.SEFX_of_SEFXlit
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T03:28:58.860521+00:00
-- url     : https://prove2.me/submissions/6d534bdd-1184-4639-b3a5-a4f9fba72719

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresEnvy
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
variable {c : Fin n → T → ℝ} {p : T → ℝ} {o : Outcome T n}
omit [Fintype T] [DecidableEq T]


theorem solution (h : SEFXlit c p o) : SEFX c p o := by
  intro i j; obtain ⟨hi,hj⟩ := h i j; refine ⟨hi,?_⟩; intro hz; right
  intro t ht; have hd := hj hz t ht
  have hc : cbar (c i) p t ≤ c i t := min_le_left _ _
  linarith
