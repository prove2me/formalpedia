-- Prove2me | solution 1 for FirstPassageLinearTransport.twoRegimeClockPotential_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:44:35.072353+00:00
-- url     : https://prove2.me/submissions/15aac2d1-fbb6-48de-8730-865e85ba3e21

import Definitions.Def_FirstPassageLinearTransport_TwoRegimeRun
import Definitions.Def_FirstPassageLinearTransport_TwoRegimeClock

set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {rHi rLo : ℝ} (hrHi : rHi < 1) (hrLo : rLo < 1)
    (S q : ℕ) :
    0 ≤ twoRegimeClockPotential rHi rLo S q := by
  have hdHi : 0 < 1 - rHi := sub_pos.mpr hrHi
  have hdLo : 0 < 1 - rLo := sub_pos.mpr hrLo
  unfold twoRegimeClockPotential
  split_ifs
  · exact add_nonneg
      (div_nonneg (Nat.cast_nonneg q) hdHi.le)
      (div_nonneg (Nat.cast_nonneg S) hdLo.le)
  · exact div_nonneg (Nat.cast_nonneg q) hdLo.le
end FirstPassageLinearTransport
