-- Prove2me | solution 1 for FairChores.SEF1_of_SEF1lit
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T03:28:49.298478+00:00
-- url     : https://prove2.me/submissions/2fe7d40e-308a-4bf3-a14c-7c70cbbc4df9

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresEnvy
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
variable {c : Fin n → T → ℝ} {p : T → ℝ} {o : Outcome T n}
omit [Fintype T] [DecidableEq T]


theorem solution (h : SEF1lit c p o) : SEF1 c p o := by
  intro i j; obtain ⟨hi,hj⟩ := h i j; refine ⟨hi,?_⟩; intro hz; right
  obtain ⟨t,ht,hd⟩ := hj hz; refine ⟨t,ht,?_⟩
  have hc : cbar (c i) p t ≤ c i t := min_le_left _ _
  linarith
