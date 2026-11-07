-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f4_turn17_factorised_operator_algebra_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T12:47:15.972938+00:00
-- url     : https://prove2.me/submissions/31eeb486-8bba-4774-90bc-4c290ed5b709

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
noncomputable section

theorem solution
    (rpos rneg v dv ddv : ℝ)
    (hODE : ddv - (rpos + rneg) * dv + rpos * rneg * v ≤ 0) :
    ddv - rpos * dv ≤ rneg * (dv - rpos * v) := by
  nlinarith [hODE]
