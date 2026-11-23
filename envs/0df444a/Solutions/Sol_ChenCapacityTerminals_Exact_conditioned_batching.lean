-- Prove2me | solution 1 for ChenCapacityTerminals.Exact.conditioned_batching
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T06:39:13.610421+00:00
-- url     : https://prove2.me/submissions/fa356b66-1e4b-4f31-a737-4f8f17c0769d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_ChenCapacityTerminals_Exact_BatchRecursion
import Theorems.Thm_ChenCapacityTerminals_Exact_terminal_group
import Theorems.Thm_ChenCapacityTerminals_Exact_exists_lawfulExactOracle
import Theorems.Thm_ChenCapacityTerminals_Exact_batching_recursion_correctness
import Theorems.Thm_ChenCapacityTerminals_Exact_batching_exact_program_realization

set_option autoImplicit false

open ChenCapacityTerminals.Exact

theorem solution :
    (∃ O, LawfulExactOracle O) ∧
    ∃ (P : ExactProgram) (C : ℝ) (k B : ℕ),
      0 < C ∧ 0 < B ∧ BatchAlgorithm P C k B := by
  refine ⟨exists_lawfulExactOracle, ?_⟩
  obtain ⟨C, k, B, hC, hB, hrec⟩ :=
    batching_recursion_correctness terminal_group
  obtain ⟨P, hP⟩ := batching_exact_program_realization C k B hrec
  exact ⟨P, C, k, B, hC, hB, hP⟩
