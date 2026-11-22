-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.log_two_le_log_analytic_conductor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:17:29.621173+00:00
-- url     : https://prove2.me/submissions/b3977039-db3b-4d2b-b908-fc5ed39f82cb

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LogTwoLeLogAnalyticConductor
import Theorems.Thm_Formalism_ZeroFreeDirichlet_one_le_modulus_real

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
theorem _root_.solution (q : ℕ) [NeZero q] (t : ℝ) : Real.log 2 ≤ Real.log ((q : ℝ) * (|t| + 2)) := by
  have h1 := one_le_modulus_real q
  have h2 := abs_nonneg t
  exact Real.log_le_log (by norm_num) (by nlinarith)
end Formalism.ZeroFreeDirichlet
