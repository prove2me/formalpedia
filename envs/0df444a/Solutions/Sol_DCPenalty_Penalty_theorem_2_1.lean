-- Prove2me | solution 1 for DCPenalty.Penalty.theorem_2_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T15:48:49.989491+00:00
-- url     : https://prove2.me/submissions/c51fd7e7-be6f-42b4-8a7e-7046d790e7aa

import Mathlib
import Definitions.Def_ClarkeGradients_MaxFunctions_HasOneSidedDirDeriv
import Definitions.Def_DCPenalty_Penalty_Problem
import Definitions.Def_DCPenalty_Penalty_Stationarity
import Definitions.Def_DCPenalty_Penalty_Algorithm
import Theorems.Thm_DCPenalty_Penalty_corollary_2_1

open Filter Topology ClarkeGradients.MaxFunctions DCPenalty.Penalty

theorem solution {n m : ℕ} (P : DCProblem n m) (hP : P.Standing)
    {xbar : EuclideanSpace ℝ (Fin n)} (hfeas : xbar ∈ P.Ω) (hact : (P.Ieq xbar).Nonempty)
    (hpscq : P.PSCQ xbar) :
    P.IsBStationary xbar ↔
      ∀ jj ∈ P.Jtup xbar, ∀ d ∈ tangentConeB (P.Y jj xbar) xbar,
        ∃ c, HasOneSidedDirDeriv P.F xbar d c ∧ 0 ≤ c := by
  obtain ⟨h1, h2⟩ := corollary_2_1 P hP hfeas hact hpscq
  have hT : tangentConeB P.Ω xbar = ⋃ jj ∈ P.Jtup xbar, tangentConeB (P.Y jj xbar) xbar :=
    h1.trans h2
  unfold DCProblem.IsBStationary
  rw [hT]
  constructor
  · rintro ⟨-, h⟩ jj hjj d hd
    exact h d (Set.mem_biUnion hjj hd)
  · intro h
    refine ⟨hfeas, fun d hd => ?_⟩
    simp only [Set.mem_iUnion] at hd
    obtain ⟨jj, hjj, hd⟩ := hd
    exact h jj hjj d hd
