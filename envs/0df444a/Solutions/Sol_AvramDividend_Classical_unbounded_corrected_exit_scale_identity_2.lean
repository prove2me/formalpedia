-- Prove2me | solution 2 for AvramDividend.Classical.unbounded_corrected_exit_scale_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T10:39:44.337966+00:00
-- url     : https://prove2.me/submissions/ebbb895b-c900-4bd7-8014-45299c4747eb

import Mathlib.Data.ENNReal.Inv
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_two_sided_exit_stopped_scale_identity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx : 0 ≤ x) (hxa : x ≤ a) :
    twoSidedExitExpectationCorrected X q a x =
      ENNReal.ofReal (W x / W a) := by
  have hWa : 0 < W a :=
    scaleFunction_strict_pos_of_unbounded_variation X q W hW hnbv a ha
  have hstop := chat04_unbounded_two_sided_exit_stopped_scale_identity
    X q hq W hW hnbv a x ha hx hxa
  have hden0 : ENNReal.ofReal (W a) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hWa)
  have hdenTop : ENNReal.ofReal (W a) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hraw :
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
      _ = ENNReal.ofReal (W x) / ENNReal.ofReal (W a) := by
          rw [hstop]
  have hconj : twoSidedExitExpectationCorrected X q a x =
      (∫⁻ ω,
        if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
            (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
          ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
        else 0 ∂P) := by
    unfold twoSidedExitExpectationCorrected
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
  calc
    twoSidedExitExpectationCorrected X q a x = _ := hconj
    _ = ENNReal.ofReal (W x) / ENNReal.ofReal (W a) := hraw
    _ = ENNReal.ofReal (W x / W a) := by
      rw [ENNReal.ofReal_div_of_pos hWa]
