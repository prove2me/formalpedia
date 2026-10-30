-- Prove2me | solution 1 for AvramDividend.Classical.two_sided_exit_before_ruin_identity_corrected
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T08:17:32.553686+00:00
-- url     : https://prove2.me/submissions/62133240-7c22-40a8-91d0-4e4fdb1e0a74

import Mathlib.Data.ENNReal.Inv
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_two_sided_exit_stopped_scale_identity
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

open AvramDividend.Classical

/-- The discounted two-sided exit expectation is the ratio of the scale
function at the starting point and at the upper barrier.

This is a conditional algebraic reduction. The substantive content is the
still-Open `two_sided_exit_stopped_scale_identity`, which carries the
continuous-time optional-stopping argument for the killed q-scale payoff. The
source reduces that identity to the ratio form asserted here.

The stopped-scale identity is stated with the raw infimum notation for the two
exit clocks, and so is the intermediate step of this proof. The exit
expectation of the target is the *corrected* one, whose clocks
`twoSidedExitUpTimeCorrected` and `twoSidedExitDownTimeCorrected` have exactly
the same bodies as `twoSidedExitUpTime` and `twoSidedExitDownTime` -- both are
the infimum of the first passage times -- so the two integrals agree, and the
agreement is discharged by unfolding the two definitions rather than by any
analytic argument.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    twoSidedExitExpectationCorrected X q a x =
      ENNReal.ofReal (W x / W a) := by
  have hWa : 0 < W a :=
    AvramDividend.Classical.scaleFunction_strict_pos_of_standing
      X hX q hq W hW a ha
  have hstop :=
    AvramDividend.Classical.two_sided_exit_stopped_scale_identity
      X hX q hq W hW a x ha hx0 hxa
  have hden0 : ENNReal.ofReal (W a) ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hWa)
  have hdenTop : ENNReal.ofReal (W a) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hdiv :
      (∫⁻ ω,
        if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
            (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
          ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
        else 0 ∂P) =
      ENNReal.ofReal (W x) / ENNReal.ofReal (W a) := by
    calc
      (∫⁻ ω,
        if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
            (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
          ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
        else 0 ∂P) =
          ((∫⁻ ω,
            if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
                (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
              ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
                (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
            else 0 ∂P) * ENNReal.ofReal (W a)) /
            ENNReal.ofReal (W a) := by
            symm
            exact ENNReal.mul_div_cancel_right hden0 hdenTop
      _ = ENNReal.ofReal (W x) / ENNReal.ofReal (W a) := by rw [hstop]
  unfold twoSidedExitExpectationCorrected
  have hconj :
      (∫⁻ ω,
        if twoSidedExitUpTimeCorrected X (a - x) ω <
            twoSidedExitDownTimeCorrected X (-x) ω then
          ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
            (twoSidedExitUpTimeCorrected X (a - x) ω))))
        else 0 ∂P) =
      (∫⁻ ω,
        if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
            (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
          ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
        else 0 ∂P) := by
    apply lintegral_congr
    intro ω
    by_cases hc :
        twoSidedExitUpTimeCorrected X (a - x) ω <
          twoSidedExitDownTimeCorrected X (-x) ω
    · have hc' :
          (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
            (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) := by
        simpa only [twoSidedExitUpTimeCorrected, twoSidedExitUpTime,
          twoSidedExitDownTimeCorrected, twoSidedExitDownTime] using hc
      simp only [if_pos hc, if_pos hc']
      rfl
    · have hc' :
          ¬ ((⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
            (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞))) := by
        simpa only [twoSidedExitUpTimeCorrected, twoSidedExitUpTime,
          twoSidedExitDownTimeCorrected, twoSidedExitDownTime] using hc
      simp only [if_neg hc, if_neg hc']
  rw [hconj]
  simpa only [ENNReal.ofReal_div_of_pos hWa] using hdiv
