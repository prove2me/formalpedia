-- Prove2me | solution 1 for Formalism.RankGapBounds.ChebyshevFactorialBounds.chebyshevThetaLe_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:27:08.229626+00:00
-- url     : https://prove2.me/submissions/872d92b9-b4d4-48ab-987f-4358c8a5e755

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
theorem _root_.solution : ChebyshevTheta := by
  intro n
  have h := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  rw [Chebyshev.theta_eq_sum_primesLE_log] at h
  exact h
end Formalism.RankGapBounds.ChebyshevFactorialBounds
