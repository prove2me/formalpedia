-- Prove2me | solution 1 for Formalism.RankGapBounds.ChebyshevFactorialBounds.harmonicLeOneAddLog_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:19:32.871874+00:00
-- url     : https://prove2.me/submissions/9eb67126-0b32-4779-b544-2bc82d915ef1

import Definitions.Def_Formalism_RankGapBounds_LargePrimeFactor
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real Finset
open Formalism Formalism.RankGapBounds Formalism.RankGapBounds.ChebyshevFactorialBounds
namespace Formalism.RankGapBounds.ChebyshevFactorialBounds
theorem _root_.solution : HarmonicLog := by
  intro n _
  have h := harmonic_le_one_add_log n
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h
  simpa only [one_div] using h
end Formalism.RankGapBounds.ChebyshevFactorialBounds
