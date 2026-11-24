-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.re_sub_le_re_of_mem_closedBall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:45:11.709916+00:00
-- url     : https://prove2.me/submissions/55889501-e8de-4b93-a104-44f90fdf764a

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LocalZerosOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution {z₀ w : ℂ} {r : ℝ} (hw : w ∈ Metric.closedBall z₀ r) : z₀.re - r ≤ w.re := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hw
  have h1 := Complex.abs_re_le_norm (w - z₀)
  have h2 := neg_abs_le (w - z₀).re
  rw [Complex.sub_re] at h1 h2
  linarith
end Formalism.ZeroFreeDirichlet
