-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.half_le_of_real_in_region
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:58:10.549354+00:00
-- url     : https://prove2.me/submissions/65a9dca8-4728-41c4-9efb-544959606a1f

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
theorem _root_.solution {c₁ : ℝ} (h : c₁ ≤ 1 / 20) {q : ℕ} [NeZero q] {β : ℝ} (hs : InRegion c₁ q (β : ℂ)) :
    1 / 2 ≤ β := by
  unfold InRegion at hs
  have hL := log_analytic_conductor_pos q (β:ℂ).im
  have h2 : (2:ℝ) ≤ (q:ℝ) * (|(β:ℂ).im| + 2) := by
    have hq : (1:ℝ) ≤ q := by
      have h1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
      exact_mod_cast h1
    have ht := abs_nonneg (β:ℂ).im
    nlinarith
  have hl2 : Real.log 2 ≤ Real.log ((q:ℝ) * (|(β:ℂ).im| + 2)) := Real.log_le_log (by norm_num) h2
  have hlt := Real.log_two_gt_d9
  have hc : c₁ / Real.log ((q:ℝ) * (|(β:ℂ).im| + 2)) ≤ 1 / 2 := by
    rw [div_le_iff₀ hL]
    linarith
  have hre : (β:ℂ).re = β := Complex.ofReal_re β
  linarith
end Formalism.ZeroFreeDirichlet
