-- Prove2me | solution 1 for BSLambda.IsTournament.disjoint_outNbrs_inNbrs
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T00:53:46.673599+00:00
-- url     : https://prove2.me/submissions/9f393716-8036-4abd-a026-59e1346a94bc

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
variable [Fintype ι]
variable {Arc : ι → ι → Bool} {i j : ι}


theorem solution (h : IsTournament Arc) (v : ι) :
    Disjoint (outNbrs Arc v) (inNbrs Arc v) := by
  apply Finset.disjoint_left.mpr
  intro j ha hb
  have a : Arc v j := by simpa [outNbrs] using ha
  have b : Arc j v := by simpa [inNbrs] using hb
  by_cases e : v = j
  · subst j; simp [h.arc_self] at a
  · rw [h.arc_eq_not_arc e, b] at a; contradiction
