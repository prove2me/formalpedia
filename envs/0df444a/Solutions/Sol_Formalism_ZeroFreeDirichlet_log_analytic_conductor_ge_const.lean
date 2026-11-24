-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.log_analytic_conductor_ge_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:44:10.026362+00:00
-- url     : https://prove2.me/submissions/31760524-4680-429a-beb0-82a762db1ce4

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LogTwoLeLogAnalyticConductor
import Theorems.Thm_Formalism_ZeroFreeDirichlet_log_two_le_log_analytic_conductor

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
theorem _root_.solution (q : ℕ) [NeZero q] (t : ℝ) : 69 / 100 ≤ Real.log ((q : ℝ) * (|t| + 2)) := by
  have h := Real.log_two_gt_d9
  have h2 := log_two_le_log_analytic_conductor q t
  linarith
end Formalism.ZeroFreeDirichlet
