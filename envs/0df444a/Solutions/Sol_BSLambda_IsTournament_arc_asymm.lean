-- Prove2me | solution 1 for BSLambda.IsTournament.arc_asymm
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T00:49:21.423147+00:00
-- url     : https://prove2.me/submissions/a70723f4-8d9c-416f-8504-640ee36c1186

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Fintype.Card
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Tournament
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open Finset
variable {ι : Type*}
open BSLambda.IsTournament
variable {Arc : ι → ι → Bool} (h : IsTournament Arc) {i j : ι}
include h


theorem solution (hij : Arc i j) : ¬ Arc j i := by
  by_cases e : i = j
  · subst j; simp [h.arc_self] at hij
  · rw [h.arc_eq_not_arc e] at hij; simpa using hij
