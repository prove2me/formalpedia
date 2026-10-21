-- Prove2me | solution 1 for FlexGroupBuy.REE.xbar1_pos_iff
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T03:09:12.056115+00:00
-- url     : https://prove2.me/submissions/08b76ef9-095b-4da6-9dc5-e4e5e99341cb

import Mathlib
import Definitions.Def_FlexGroupBuy_REE_Model

open FlexGroupBuy.REE

theorem solution (P : Params) (hP : P.Standing) (N : ℕ) (hN : 1 ≤ N) :
    0 < xbar1 P N ↔ Nbar2 P < N := by
  unfold xbar1 Nbar2
  constructor <;> intro h <;> linarith
