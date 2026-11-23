-- Prove2me | solution 1 for ChvatalOneHard398.SAT.reduction_solverConsequence
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:55:24.128779+00:00
-- url     : https://prove2.me/submissions/f2dbc7ac-3c0a-4a4b-b7ec-57afe3a2f4a3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ChvatalOneHard398_SAT_Oracle
import Theorems.Thm_ChvatalOneHard398_SAT_oracleRun_output_polyTime

open ChvatalOneHard398.SAT
open OnlineCRS.Combine

theorem solution : ChvatalOneHard398.SAT.BDDReduction ChvatalOneHard398.SAT.TargetPromise → ChvatalOneHard398.SAT.SolverConsequence := by
  rintro ⟨A, rounds, hpoly, hcorrect⟩
  intro f hf hforacle
  let g : BDDInput → List ℚ := fun x =>
    (oracleRun A f x (rounds.eval (encBDD x).length) []).output.getD []
  refine ⟨g, ?_, ?_⟩
  · exact oracleRun_output_polyTime encBDD encFormula encOutput A rounds f []
      hpoly.1 hf
  · intro x hx
    obtain ⟨v, hv, hvcorrect⟩ := hcorrect f hforacle x hx
    have hg : g x = v := by
      dsimp [g]
      rw [hv]
      rfl
    rw [hg]
    exact hvcorrect
