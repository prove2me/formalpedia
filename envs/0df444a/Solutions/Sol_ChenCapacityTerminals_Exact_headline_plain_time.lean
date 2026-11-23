-- Prove2me | solution 1 for ChenCapacityTerminals.Exact.headline_plain_time
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T05:42:56.609234+00:00
-- url     : https://prove2.me/submissions/4f202ad3-1ea3-4018-98ee-4bc4462fe576
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_ChenCapacityTerminals_Exact_headline_oracle_reduction
import Theorems.Thm_ChenCapacityTerminals_Exact_deterministic_integer_flow
import Theorems.Thm_ChenCapacityTerminals_Exact_compile_flow_oracle

set_option autoImplicit false

open ChenCapacityTerminals.Exact

theorem solution : ∃ T : List TrulySubcubicAPSP.Instr, HeadlineTime T := by
  obtain ⟨P, hP⟩ := headline_oracle_reduction
  obtain ⟨S, hS⟩ := deterministic_integer_flow
  exact compile_flow_oracle P S hP hS
