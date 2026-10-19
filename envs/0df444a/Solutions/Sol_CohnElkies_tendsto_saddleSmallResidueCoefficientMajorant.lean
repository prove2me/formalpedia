-- Prove2me | solution 1 for CohnElkies.tendsto_saddleSmallResidueCoefficientMajorant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.981105+00:00
-- url     : https://prove2.me/submissions/329dae92-6a5f-4faf-950b-6f2743b944b7

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_tendsto_saddleSmallResidueTruncation_sq_div
import Theorems.Thm_CohnElkies_tendsto_saddleLogWindowPolynomial_exp_neg

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    (K C : ℝ) :
    Tendsto (saddleSmallResidueCoefficientMajorant K C)
      atTop (𝓝 0) := by
  have hscaled :
      Tendsto
        (fun ℓ : ℝ =>
          K * (saddleSmallResidueTruncation ℓ : ℝ) ^ 2 / ℓ)
        atTop (𝓝 0) := by
    convert! tendsto_saddleSmallResidueTruncation_sq_div.const_mul K
      using 1
    · funext ℓ
      ring
    · norm_num
  have hfactor :
      Tendsto
        (fun ℓ : ℝ =>
          Real.exp
            (K * (saddleSmallResidueTruncation ℓ : ℝ) ^ 2 / ℓ))
        atTop (𝓝 1) := by
    simpa using! hscaled.rexp
  have hwindow :=
    (tendsto_saddleLogWindowPolynomial_exp_neg C).comp
      Real.tendsto_log_atTop
  have hwindowScaled := hwindow.const_mul
    (Real.exp (2 * C))
  have htotal :=
    (hfactor.const_mul K).mul hwindowScaled
  convert! htotal using 1
  · funext ℓ
    unfold saddleSmallResidueCoefficientMajorant
    rw [show
      2 * C - (3 / 4 : ℝ) * Real.log ℓ =
        2 * C + (-(3 / 4 : ℝ)) * Real.log ℓ by ring,
      Real.exp_add]
    simp only [Function.comp_apply]
    ring
  · norm_num
end CohnElkies
