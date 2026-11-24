-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.re_ge_of_mem_closedBall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:45:06.203842+00:00
-- url     : https://prove2.me/submissions/f1060820-544a-4ead-ab0b-b8720dcf18ee

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LogTwoLeLogAnalyticConductor

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
  rw [Metric.mem_closedBall, Complex.dist_eq] at hw
  have h1 := Complex.abs_re_le_norm (w - z₀)
  rw [Complex.sub_re] at h1
  have h2 := neg_abs_le (w.re - z₀.re)
  linarith
end Formalism.ZeroFreeDirichlet
