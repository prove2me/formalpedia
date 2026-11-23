-- Prove2me | solution 1 for ChenCapacityTerminals.Exact.directed_minimum_cut
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T05:28:30.174819+00:00
-- url     : https://prove2.me/submissions/87730fc6-214f-4a5f-bf96-ec47258974b7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_ChenCapacityTerminals_Exact_headline_oracle_reduction
import Theorems.Thm_ChenCapacityTerminals_Exact_headline_plain_time

set_option autoImplicit false

open ChenCapacityTerminals.Exact

theorem solution :
    (∃ P : WordProgram, HeadlineReduction P) ∧
    ∃ P : List TrulySubcubicAPSP.Instr, HeadlineTime P := by
  exact ⟨headline_oracle_reduction, headline_plain_time⟩
