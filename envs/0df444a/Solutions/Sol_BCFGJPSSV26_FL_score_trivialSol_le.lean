-- Prove2me | solution 1 for BCFGJPSSV26.FL.score_trivialSol_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T17:52:53.310915+00:00
-- url     : https://prove2.me/submissions/d713a0cd-9599-49d8-ad66-0ecddaac65d1

module

public import Definitions.Def_BCFGJPSSV26_FL_Algorithm
public import Definitions.Def_BCFGJPSSV26_FL_Select
import all Definitions.Def_BCFGJPSSV26_FL_Select

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.FL

open Finset Greedy

variable {I : Instance}

/-- The trivial solution meets the bound if it has at most as many facilities as an optimal
set, or if `f = 0`. -/
theorem score_trivialSol_le (hI : I.Valid) (hn : 1 ≤ I.n) {f : ℚ} (hf : 0 ≤ f)
    {O : Finset (Fin I.m)} (hO : O.Nonempty) (hopt : I.optFL f = I.cost O + f * O.card)
    (h : (trivialSol (toRaw I)).length ≤ O.card ∨ f = 0) :
    (score (toRaw I) f (trivialSol (toRaw I)) : ℝ) ≤ (lmpC : ℝ) * I.optFL f := by
  have hT := isCenterList_trivialSol hI hn
  rw [score_cast hT.1 hT.2.2, hopt]
  have h1 := cost_trivialSol_le_cost hI hn hO
  have h2 := Instance.cost_nonneg' hI O
  have hl := one_le_lmpC
  have hf' : (0 : ℝ) ≤ f := by exact_mod_cast hf
  have h3 : (lmpC : ℝ) * f * (trivialSol (toRaw I)).length ≤ (lmpC : ℝ) * f * O.card := by
    rcases h with h | h
    · have : ((trivialSol (toRaw I)).length : ℝ) ≤ O.card := by exact_mod_cast h
      exact mul_le_mul_of_nonneg_left this (by positivity)
    · rw [h]
      simp
  nlinarith

end BCFGJPSSV26.FL

end

public section

theorem solution : type_of% @BCFGJPSSV26.FL.score_trivialSol_le := @BCFGJPSSV26.FL.score_trivialSol_le
