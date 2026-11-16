-- Prove2me | solution 1 for FairShareAlmostAll.Slack.Supplement.fractional_certificate
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T21:11:16.76251+00:00
-- url     : https://prove2.me/submissions/b1143625-68d3-489c-a583-de11fb970d9c

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic
import Definitions.Def_FairShareAlmostAll_Slack_FiniteAllocation
import Definitions.Def_FairShareAlmostAll_Slack_Supplement_ThirteenGoods

open FairShareAlmostAll.Slack AnyPriceShare.Bidding
open FairShareAlmostAll.Slack.Supplement

theorem solution :
    (∀ P : Fin 13, 153 ≤ addVal thirteenValue (thirteenBundle P)) ∧
    ∑ P : Fin 13, thirteenWeight P = 51 / 10 ∧
    ∀ g : Fin 13,
      ∑ P ∈ Finset.univ.filter (fun P : Fin 13 => g ∈ thirteenBundle P),
        thirteenWeight P = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro P
    fin_cases P <;> simp [addVal, thirteenBundle, thirteenValue] <;> norm_num
  · simp [Fin.sum_univ_succ, thirteenWeight]; norm_num
  · intro g
    rw [Finset.sum_filter]
    fin_cases g <;> simp [Fin.sum_univ_succ, thirteenBundle, thirteenWeight] <;> norm_num
