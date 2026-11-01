-- Prove2me | solution 1 for DCPenalty.Penalty.corollary_2_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T15:48:49.428268+00:00
-- url     : https://prove2.me/submissions/f8b340d0-2847-49ea-86f8-bae337801fa2

import Mathlib
import Definitions.Def_ClarkeGradients_MaxFunctions_HasOneSidedDirDeriv
import Definitions.Def_DCPenalty_Penalty_Problem
import Definitions.Def_DCPenalty_Penalty_Stationarity
import Definitions.Def_DCPenalty_Penalty_Algorithm
import Theorems.Thm_DCPenalty_Penalty_eq_2_1
import Theorems.Thm_DCPenalty_Penalty_proposition_2_1

open Filter Topology ClarkeGradients.MaxFunctions DCPenalty.Penalty

theorem solution {n m : ℕ} (P : DCProblem n m) (hP : P.Standing)
    {xbar : EuclideanSpace ℝ (Fin n)} (hfeas : xbar ∈ P.Ω) (hact : (P.Ieq xbar).Nonempty)
    (hpscq : P.PSCQ xbar) :
    tangentConeB P.Ω xbar = ⋃ jj ∈ P.Jtup xbar, P.C jj xbar ∧
      ⋃ jj ∈ P.Jtup xbar, P.C jj xbar = ⋃ jj ∈ P.Jtup xbar, tangentConeB (P.Y jj xbar) xbar := by
  have hp := fun jj (hjj : jj ∈ P.Jtup xbar) =>
    proposition_2_1 P hP hfeas hact hjj (hpscq jj hjj)
  constructor
  · rw [eq_2_1 P hP xbar hfeas]
    refine Set.iUnion₂_congr (fun jj hjj => (hp jj hjj).2)
  · refine Set.iUnion₂_congr (fun jj hjj => ?_)
    rw [(hp jj hjj).1, (hp jj hjj).2]
