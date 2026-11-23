-- Prove2me | solution 1 for ChvatalOneHard398.SAT.theorem_26
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:30:13.941565+00:00
-- url     : https://prove2.me/submissions/1871dc63-4da0-4af8-8cc2-3917e95df7be
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ChvatalOneHard398_SAT_Oracle
import Theorems.Thm_ChvatalOneHard398_SAT_lemma_25
import Theorems.Thm_ChvatalOneHard398_SAT_proposition_16
import Theorems.Thm_ChvatalOneHard398_SAT_theorem_26_queryDecoder

open ChvatalOneHard398.SAT

theorem solution :
    ∃ (A : OracleAlg BDDInput Formula (List ℚ)) (rounds : Polynomial ℕ),
      IsPolyOracle encBDD encFormula encOutput A rounds ∧ SolvesBDDWith A rounds ThinQuery ∧
      ∀ orc x, ∀ F ∈ (oracleRun A orc x (rounds.eval (encBDD x).length) []).queries,
        ConstructedQuery F := by
  obtain ⟨f, hf, hf_correct⟩ := lemma_25
  exact theorem_26_queryDecoder f hf hf_correct
