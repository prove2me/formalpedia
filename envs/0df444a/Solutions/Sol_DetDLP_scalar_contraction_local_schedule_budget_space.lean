-- Prove2me | solution 1 for DetDLP.scalar_contraction_local_schedule_budget_space
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T23:01:08.692502+00:00
-- url     : https://prove2.me/submissions/e0f5d75b-0599-4416-a2db-44ee2d04d2a6

import Definitions.Def_DetDLP_ContractionContinuation
import Definitions.Def_DetDLP_BTN
import Definitions.Def_OAIQ081S000

set_option autoImplicit false

open DetDLP
open DetDLP.ContinuationSchedule
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation

theorem solution
    (β : ℕ) (desc : List Bool) (w : List Bool) (cap0 U overhead : ℕ) :
    ∃ K : ℕ,
      max cap0 (max U overhead) + 6 * w.length + 13 ≤ K * (β + desc.length + 1) ^ K := by
  set W : ℕ := max cap0 (max U overhead) + 6 * w.length + 13
  refine ⟨W + 1, ?_⟩
  have hbase : 1 ≤ β + desc.length + 1 := Nat.succ_le_succ (Nat.zero_le _)
  have hpow : 1 ≤ (β + desc.length + 1) ^ (W + 1) :=
    Nat.one_le_pow (W + 1) (β + desc.length + 1) hbase
  have hW : W ≤ W + 1 := Nat.le_succ W
  exact Nat.le_trans hW (Nat.le_mul_of_pos_right (W + 1) (lt_of_lt_of_le Nat.zero_lt_one hpow))
