-- Prove2me | solution 1 for CohnElkies.saddleSourceCenteredMinusIntegrand_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:29.488992+00:00
-- url     : https://prove2.me/submissions/f8cbbb75-d076-4e90-a81b-663c3a4de684

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleSourceContourEnvelopeScale_pos
import Theorems.Thm_CohnElkies_saddleSourceCenteredMinusIntegrand_sourcePointwise

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped ContDiff FourierTransform Interval RealInnerProductSpace
  SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution
    {ε ℓ u : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ) (hu : -1 < u)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (v : ℝ) :
    Integrable (saddleSourceCenteredMinusIntegrand ε ℓ u v) := by
  let a : ℝ := ℓ * (1 + u)
  let c : ℂ :=
    ((Real.exp (-(ℓ * (1 + u) * v)) *
      saddleSourceContourEnvelopeScale ε ℓ u : ℝ) : ℂ)
  have ha : 0 < a := by
    try dsimp [a]
    have : 0 < 1 + u := by linarith
    positivity
  have hline :=
    minusSaddleMellinData_shiftedLine_weighted_integrable
      (a := a) (r := Real.exp v)
      hε hℓ horder
      (fun n => saddlePositiveContour_ne_pole ha n)
      (Real.exp_pos v)
  have hcomp := hline.comp_mul_left'
    (neg_ne_zero.mpr hℓ.ne')
  have hcontour : Integrable (fun T : ℝ =>
      saddleMellinInversePower (Real.exp v)
          (saddleSourceMellinContour ℓ u T) *
        minusSaddleMellinData ε ℓ
          (saddleSourceMellinContour ℓ u T)) := by
    apply hcomp.congr
    filter_upwards [] with T
    have harg :
        (a : ℂ) + (((-ℓ) * T : ℝ) : ℂ) * Complex.I =
          saddleSourceMellinContour ℓ u T := by
      try dsimp [a]
      unfold saddleSourceMellinContour
      push_cast
      ring
    rw [harg]
  have hscaled : Integrable
      (fun T : ℝ => c *
        saddleSourceCenteredMinusIntegrand ε ℓ u v T) := by
    apply hcontour.congr
    filter_upwards [] with T
    exact saddleSourceCenteredMinusIntegrand_sourcePointwise
      hℓ hu v T
  have hc : c ≠ 0 := by
    try dsimp [c]
    apply Complex.ofReal_ne_zero.mpr
    exact (mul_pos (Real.exp_pos _)
      (saddleSourceContourEnvelopeScale_pos
        (ε := ε) hℓ hu)).ne'
  have hinverse := hscaled.const_mul c⁻¹
  apply hinverse.congr
  filter_upwards [] with T
  rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
end CohnElkies
