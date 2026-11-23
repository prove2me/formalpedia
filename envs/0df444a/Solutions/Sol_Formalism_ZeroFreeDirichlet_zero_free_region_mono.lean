-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.zero_free_region_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:57:57.643992+00:00
-- url     : https://prove2.me/submissions/0fa4c5bb-10eb-4a1e-a9ee-07aba2adb512

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SiegelWalfiszOf
import Theorems.Thm_Formalism_ZeroFreeDirichlet_log_analytic_conductor_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution {c c' : ℝ} (h : c ≤ c') {q : ℕ} [NeZero q] {s : ℂ} (hs : InRegion c q s) :
    InRegion c' q s := by
  unfold InRegion at hs ⊢
  have hL := log_analytic_conductor_pos q s.im
  have h2 : c / Real.log (↑q * (|s.im| + 2)) ≤ c' / Real.log (↑q * (|s.im| + 2)) := by
    first
      | exact div_le_div_of_nonneg_right h hL.le
      | exact (div_le_div_iff_of_pos_right hL).mpr h
  linarith
end Formalism.ZeroFreeDirichlet
