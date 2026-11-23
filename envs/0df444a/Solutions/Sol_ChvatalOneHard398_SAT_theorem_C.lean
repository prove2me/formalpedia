-- Prove2me | solution 1 for ChvatalOneHard398.SAT.theorem_C
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:40:13.11305+00:00
-- url     : https://prove2.me/submissions/7fc887d7-d901-4a46-af85-fde71cb75b5e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ChvatalOneHard398_SAT_Oracle
import Theorems.Thm_ChvatalOneHard398_SAT_theorem_26
import Theorems.Thm_ChvatalOneHard398_SAT_thin_query_targetPromise
import Theorems.Thm_ChvatalOneHard398_SAT_reduction_solverConsequence

open ChvatalOneHard398.SAT

theorem solution : BDDReduction TargetPromise ∧ SolverConsequence := by
  rcases theorem_26 with ⟨A, rounds, hpoly, hsolve, hqueries⟩
  have hred : BDDReduction TargetPromise := by
    refine ⟨A, rounds, hpoly, ?_⟩
    intro orc horc
    apply hsolve orc
    intro F hF
    exact horc F (thin_query_targetPromise F hF)
  exact ⟨hred, reduction_solverConsequence hred⟩