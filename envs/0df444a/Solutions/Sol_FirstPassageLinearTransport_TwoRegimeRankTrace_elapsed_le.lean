-- Prove2me | solution 1 for FirstPassageLinearTransport.TwoRegimeRankTrace.elapsed_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:48:47.639222+00:00
-- url     : https://prove2.me/submissions/b45f6bbd-07c5-4ec2-bed8-0822979ae02e

import Definitions.Def_FirstPassageLinearTransport_TwoRegimeRun
import Definitions.Def_FirstPassageLinearTransport_TwoRegimeClock
import Theorems.Thm_FirstPassageLinearTransport_twoRegimeClockPotential_nonneg
import Theorems.Thm_FirstPassageLinearTransport_TwoRegimeRankTrace_elapsed_add_potential_le

set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section
namespace FirstPassageLinearTransport
namespace TwoRegimeRankTrace
theorem _root_.solution
    {rHi rLo : ℝ} {S M elapsed q : ℕ}
    (hrHi0 : 0 ≤ rHi) (hrHi1 : rHi < 1)
    (hrLo1 : rLo < 1)
    (htrace : TwoRegimeRankTrace rHi rLo S M elapsed q) :
    (elapsed : ℝ) ≤
      (M : ℝ) / (1 - rHi) + (S : ℝ) / (1 - rLo) := by
  have hmain := htrace.elapsed_add_potential_le
    hrHi0 hrHi1 hrLo1
  have hpot := twoRegimeClockPotential_nonneg hrHi1 hrLo1 S q
  linarith
end TwoRegimeRankTrace
end FirstPassageLinearTransport
