-- Prove2me | solution 1 for Freiman.middle_secondary_four_separations
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-10T09:26:41.804756+00:00
-- url     : https://prove2.me/submissions/2645776d-132a-414f-9fab-90b30e0b8182

import Definitions.Def_Freiman_middleRoots
import Theorems.Thm_Freiman_gap_tail_first_difference
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
open Freiman
set_option autoImplicit false
set_option maxHeartbeats 600000
private theorem sep_5 (a : ℤ→ℕ+) (ha : middleCompatible (middleRoot 5) a) :
    cfValue (fun n : ℕ => a (-(n:ℤ)-1)) > cfValue (fun n : ℕ => a ((n:ℤ)+2)) := by
  have hl0 := ha.2.1 0 (by norm_num [middleRoot, middleRootList])
  have hr0 := ha.2.2.1 1 (by norm_num [middleRoot, middleRootList])
  norm_num [middleRoot, middleRootList] at hl0 hr0
  apply (gap_tail_first_difference (fun n : ℕ => a ((n:ℤ)+2))
    (fun n : ℕ => a (-(n:ℤ)-1)) 0 ?_ ?_).2
  · norm_num [hl0, hr0] <;> decide
  · intro k hk
    omega
  · norm_num [hl0, hr0] <;> decide
private theorem sep_6 (a : ℤ→ℕ+) (ha : middleCompatible (middleRoot 6) a) :
    cfValue (fun n : ℕ => a (-(n:ℤ)-1)) > cfValue (fun n : ℕ => a ((n:ℤ)+2)) := by
  have hl0 := ha.2.1 0 (by norm_num [middleRoot, middleRootList])
  have hr0 := ha.2.2.1 1 (by norm_num [middleRoot, middleRootList])
  norm_num [middleRoot, middleRootList] at hl0 hr0
  apply (gap_tail_first_difference (fun n : ℕ => a ((n:ℤ)+2))
    (fun n : ℕ => a (-(n:ℤ)-1)) 0 ?_ ?_).2
  · norm_num [hl0, hr0] <;> decide
  · intro k hk
    omega
  · norm_num [hl0, hr0] <;> decide
private theorem sep_7 (a : ℤ→ℕ+) (ha : middleCompatible (middleRoot 7) a) :
    cfValue (fun n : ℕ => a (-(n:ℤ)-1)) > cfValue (fun n : ℕ => a ((n:ℤ)+2)) := by
  have hl0 := ha.2.1 0 (by norm_num [middleRoot, middleRootList])
  have hr0 := ha.2.2.1 1 (by norm_num [middleRoot, middleRootList])
  have hl1 := ha.2.1 1 (by norm_num [middleRoot, middleRootList])
  have hr1 := ha.2.2.1 2 (by norm_num [middleRoot, middleRootList])
  have hl2 := ha.2.1 2 (by norm_num [middleRoot, middleRootList])
  have hr2 := ha.2.2.1 3 (by norm_num [middleRoot, middleRootList])
  have hl3 := ha.2.1 3 (by norm_num [middleRoot, middleRootList])
  have hr3 := ha.2.2.1 4 (by norm_num [middleRoot, middleRootList])
  norm_num [middleRoot, middleRootList] at hl0 hr0 hl1 hr1 hl2 hr2 hl3 hr3
  apply (gap_tail_first_difference (fun n : ℕ => a ((n:ℤ)+2))
    (fun n : ℕ => a (-(n:ℤ)-1)) 3 ?_ ?_).2
  · norm_num [hl3, hr3] <;> decide
  · intro k hk
    interval_cases k <;> simp_all
  · norm_num [hl3, hr3] <;> decide
private theorem sep_8 (a : ℤ→ℕ+) (ha : middleCompatible (middleRoot 8) a) :
    cfValue (fun n : ℕ => a (-(n:ℤ)-1)) > cfValue (fun n : ℕ => a ((n:ℤ)+2)) := by
  have hl0 := ha.2.1 0 (by norm_num [middleRoot, middleRootList])
  have hr0 := ha.2.2.1 1 (by norm_num [middleRoot, middleRootList])
  have hl1 := ha.2.1 1 (by norm_num [middleRoot, middleRootList])
  have hr1 := ha.2.2.1 2 (by norm_num [middleRoot, middleRootList])
  have hl2 := ha.2.1 2 (by norm_num [middleRoot, middleRootList])
  have hr2 := ha.2.2.1 3 (by norm_num [middleRoot, middleRootList])
  have hl3 := ha.2.1 3 (by norm_num [middleRoot, middleRootList])
  have hr3 := ha.2.2.1 4 (by norm_num [middleRoot, middleRootList])
  norm_num [middleRoot, middleRootList] at hl0 hr0 hl1 hr1 hl2 hr2 hl3 hr3
  apply (gap_tail_first_difference (fun n : ℕ => a ((n:ℤ)+2))
    (fun n : ℕ => a (-(n:ℤ)-1)) 3 ?_ ?_).2
  · norm_num [hl3, hr3] <;> decide
  · intro k hk
    interval_cases k <;> simp_all
  · norm_num [hl3, hr3] <;> decide
private theorem sep_9 (a : ℤ→ℕ+) (ha : middleCompatible (middleRoot 9) a) :
    cfValue (fun n : ℕ => a (-(n:ℤ)-1)) > cfValue (fun n : ℕ => a ((n:ℤ)+2)) := by
  have hl0 := ha.2.1 0 (by norm_num [middleRoot, middleRootList])
  have hr0 := ha.2.2.1 1 (by norm_num [middleRoot, middleRootList])
  have hl1 := ha.2.1 1 (by norm_num [middleRoot, middleRootList])
  have hr1 := ha.2.2.1 2 (by norm_num [middleRoot, middleRootList])
  have hl2 := ha.2.1 2 (by norm_num [middleRoot, middleRootList])
  have hr2 := ha.2.2.1 3 (by norm_num [middleRoot, middleRootList])
  have hl3 := ha.2.1 3 (by norm_num [middleRoot, middleRootList])
  have hr3 := ha.2.2.1 4 (by norm_num [middleRoot, middleRootList])
  norm_num [middleRoot, middleRootList] at hl0 hr0 hl1 hr1 hl2 hr2 hl3 hr3
  apply (gap_tail_first_difference (fun n : ℕ => a ((n:ℤ)+2))
    (fun n : ℕ => a (-(n:ℤ)-1)) 3 ?_ ?_).2
  · norm_num [hl3, hr3] <;> decide
  · intro k hk
    interval_cases k <;> simp_all
  · norm_num [hl3, hr3] <;> decide
private theorem sep_10 (a : ℤ→ℕ+) (ha : middleCompatible (middleRoot 10) a) :
    cfValue (fun n : ℕ => a (-(n:ℤ)-1)) > cfValue (fun n : ℕ => a ((n:ℤ)+2)) := by
  have hl0 := ha.2.1 0 (by norm_num [middleRoot, middleRootList])
  have hr0 := ha.2.2.1 1 (by norm_num [middleRoot, middleRootList])
  have hl1 := ha.2.1 1 (by norm_num [middleRoot, middleRootList])
  have hr1 := ha.2.2.1 2 (by norm_num [middleRoot, middleRootList])
  have hl2 := ha.2.1 2 (by norm_num [middleRoot, middleRootList])
  have hr2 := ha.2.2.1 3 (by norm_num [middleRoot, middleRootList])
  have hl3 := ha.2.1 3 (by norm_num [middleRoot, middleRootList])
  have hr3 := ha.2.2.1 4 (by norm_num [middleRoot, middleRootList])
  norm_num [middleRoot, middleRootList] at hl0 hr0 hl1 hr1 hl2 hr2 hl3 hr3
  apply (gap_tail_first_difference (fun n : ℕ => a ((n:ℤ)+2))
    (fun n : ℕ => a (-(n:ℤ)-1)) 3 ?_ ?_).2
  · norm_num [hl3, hr3] <;> decide
  · intro k hk
    interval_cases k <;> simp_all
  · norm_num [hl3, hr3] <;> decide
private theorem sep_11 (a : ℤ→ℕ+) (ha : middleCompatible (middleRoot 11) a) :
    cfValue (fun n : ℕ => a (-(n:ℤ)-1)) > cfValue (fun n : ℕ => a ((n:ℤ)+2)) := by
  have hl0 := ha.2.1 0 (by norm_num [middleRoot, middleRootList])
  have hr0 := ha.2.2.1 1 (by norm_num [middleRoot, middleRootList])
  norm_num [middleRoot, middleRootList] at hl0 hr0
  apply (gap_tail_first_difference (fun n : ℕ => a ((n:ℤ)+2))
    (fun n : ℕ => a (-(n:ℤ)-1)) 0 ?_ ?_).2
  · norm_num [hl0, hr0] <;> decide
  · intro k hk
    omega
  · norm_num [hl0, hr0] <;> decide
private theorem sep_13 (a : ℤ→ℕ+) (ha : middleCompatible (middleRoot 13) a) :
    cfValue (fun n : ℕ => a (-(n:ℤ)-1)) > cfValue (fun n : ℕ => a ((n:ℤ)+2)) := by
  have hl0 := ha.2.1 0 (by norm_num [middleRoot, middleRootList])
  have hr0 := ha.2.2.1 1 (by norm_num [middleRoot, middleRootList])
  norm_num [middleRoot, middleRootList] at hl0 hr0
  apply (gap_tail_first_difference (fun n : ℕ => a ((n:ℤ)+2))
    (fun n : ℕ => a (-(n:ℤ)-1)) 0 ?_ ?_).2
  · norm_num [hl0, hr0] <;> decide
  · intro k hk
    omega
  · norm_num [hl0, hr0] <;> decide

theorem solution :
    ∀ (r : Fin 15) (a : ℤ→ℕ+), middleCompatible (middleRoot r) a → (r.val∈[5,6,7,8,9,10,11,13]) →
      cfValue (fun n : ℕ => a (-(n:ℤ)-1)) > cfValue (fun n : ℕ => a ((n:ℤ)+2)) := by
  intro r a ha hr
  fin_cases r <;> norm_num at hr <;> first | exact sep_5 a ha | exact sep_6 a ha | exact sep_7 a ha | exact sep_8 a ha | exact sep_9 a ha | exact sep_10 a ha | exact sep_11 a ha | exact sep_13 a ha
#print axioms solution
