-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.log_analytic_conductor_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:49:10.794824+00:00
-- url     : https://prove2.me/submissions/8e4ce4d4-f541-45b7-a816-5fc93ee8163e

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_PerronHorizontalSegmentBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution (q : ℕ) [NeZero q] (u T : ℝ) (hu : |u| ≤ T) :
    Real.log ((q : ℝ) * (|u| + 2)) ≤ Real.log ((q : ℝ) * (T + 2)) := by
  have hq : (1:ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  apply Real.log_le_log
  · nlinarith [abs_nonneg u]
  · exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
end Formalism.ZeroFreeDirichlet
