-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_11_no_terminal_payment_if_clock_ended
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:16:00.40383+00:00
-- url     : https://prove2.me/submissions/8d5bef6e-2bb9-4eeb-b011-b3514f8cac99

import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Positive terminal dividend payment is impossible after clock expiry. -/
theorem solution
    (σ : ℝ≥0∞) (T : ℝ) (hT : 0 < T)
    (hσ : σ ≤ ENNReal.ofReal T) :
    paymentTimes σ ∩ {T} = ∅ := by
  ext t
  constructor
  · intro ht
    have htT : t = T := ht.2
    subst t
    rcases ht.1.2 with hzero | hlt
    · exact ((ne_of_gt hT) hzero).elim
    · exact ((not_lt_of_ge hσ) hlt).elim
  · intro ht
    exact ht.elim
