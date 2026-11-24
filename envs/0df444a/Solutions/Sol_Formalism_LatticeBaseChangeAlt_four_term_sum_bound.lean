-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.four_term_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:35:30.132033+00:00
-- url     : https://prove2.me/submissions/441dc264-fe74-4cd2-8968-f3278ef2167a

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_FourTermSumBoundOfParameters
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_FourTermSumBoundOfParameters

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LatticeBaseChangeAlt
namespace Formalism.LatticeBaseChangeAlt
theorem _root_.solution : FourTermSumBound := by
  intro d PP D κ T c RR ga C k f b m δ₂ hd hT hga hPP hD hR hκ h0 h1 h2 h3
  have e1 : PP ^ 2 * (D ^ 3 * κ / T) ≤ PP ^ 2 * D ^ 3 * C * k * f * b / T := by
    have : PP ^ 2 * D ^ 3 * C * k * f * b / T = PP ^ 2 * (D ^ 3 * (C * k * f * b) / T) := by ring
    rw [this]
    gcongr
  have e3 : PP ^ 2 * ((RR ^ 2 * c + 1 / T) * κ / ga) ≤
      PP ^ 2 * (RR ^ 2 * c + 1 / T) * C * k * f * b / ga := by
    have : PP ^ 2 * (RR ^ 2 * c + 1 / T) * C * k * f * b / ga =
        PP ^ 2 * ((RR ^ 2 * c + 1 / T) * (C * k * f * b) / ga) := by ring
    rw [this]
    gcongr
  have tot : PP ^ 2 * (D ^ 3 * κ / T + T * c + (RR ^ 2 * c + 1 / T) * κ / ga) + PP ^ 3 * T ≤
      f * m * b * δ₂ := by
    have : PP ^ 2 * (D ^ 3 * κ / T + T * c + (RR ^ 2 * c + 1 / T) * κ / ga) =
        PP ^ 2 * (D ^ 3 * κ / T) + PP ^ 2 * T * c + PP ^ 2 * ((RR ^ 2 * c + 1 / T) * κ / ga) := by
      ring
    rw [this]
    linarith
  calc d * PP ^ 2 * (D ^ 3 * κ / T + T * c + (RR ^ 2 * c + 1 / T) * κ / ga) + d * PP ^ 3 * T
      = d * (PP ^ 2 * (D ^ 3 * κ / T + T * c + (RR ^ 2 * c + 1 / T) * κ / ga) + PP ^ 3 * T) := by
        ring
    _ ≤ d * (f * m * b * δ₂) := mul_le_mul_of_nonneg_left tot hd
    _ = d * f * m * b * δ₂ := by ring
end Formalism.LatticeBaseChangeAlt
