-- Prove2me | solution 1 for BSLambda.IsTournament.outNbrs_union_inNbrs
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T00:53:45.681598+00:00
-- url     : https://prove2.me/submissions/ee294793-22ed-4817-b077-b871c6362743

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
variable [DecidableEq ι]
variable {Arc : ι → ι → Bool} {i j l u v : ι}
open BSLambda.IsTournament
variable (h : IsTournament Arc)
include h


theorem solution (v : ι) : outNbrs Arc v ∪ inNbrs Arc v = univ.erase v := by
  ext j; by_cases e : j = v
  · subst j; simp [outNbrs,inNbrs,h.arc_self]
  · rw [Finset.mem_union]; simp only [outNbrs,inNbrs,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_erase]; rw [h.arc_eq_not_arc e]; cases Arc v j <;> simp [e]
