-- Prove2me | solution 1 for Formalism.ZF.exp_mul_rpow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:42:13.450321+00:00
-- url     : https://prove2.me/submissions/d7a98a80-336b-404c-867c-c5c882639f30

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_NormIntegralComplLe

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
open Formalism Formalism.ZF
namespace Formalism.ZF
theorem _root_.solution (y c L s : ℝ) (hy : 0 < y) (hℓ : Real.log y = s ^ 2) (hc : 0 < c)
    (hc2 : c ≤ 1 / 2) (hL : 0 < L) (hLs : L ≤ c * s / 2) (hs : 0 < s) :
    Real.exp (c * s / 4) * y ^ (1 - c / L) ≤ y * Real.exp (-(c * s / 4)) := by
  have hy' : y = Real.exp (s ^ 2) := by rw [← hℓ, Real.exp_log hy]
  rw [Real.rpow_def_of_pos hy, hℓ]
  conv_rhs => rw [hy']
  rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  have key : c * s / 2 ≤ s ^ 2 * (c / L) := by
    rw [show s ^ 2 * (c / L) = (c * s ^ 2) / L by ring, le_div_iff₀ hL]
    have hcs : 0 < c * s := mul_pos hc hs
    have hL4 : L ≤ s := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hL4 hcs.le]
  nlinarith [key]
end Formalism.ZF
