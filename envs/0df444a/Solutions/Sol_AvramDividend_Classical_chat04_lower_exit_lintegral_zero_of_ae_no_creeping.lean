-- Prove2me | solution 1 for AvramDividend.Classical.chat04_lower_exit_lintegral_zero_of_ae_no_creeping
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T20:34:27.56598+00:00
-- url     : https://prove2.me/submissions/c0a4a239-f4cd-4280-9aba-bbc219f65952

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_lower_exit_scale_creeping_atom
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ)
    (hNoCreep : ∀ᵐ ω ∂P,
      twoSidedExitDownTime X (-x) ω <
        twoSidedExitUpTime X (a - x) ω →
        x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω ≠ 0) :
    (∫⁻ ω,
      if twoSidedExitDownTime X (-x) ω <
          twoSidedExitUpTime X (a - x) ω then
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitDownTime X (-x) ω).toReal))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω))
      else 0 ∂P) = 0 := by
  calc
    (∫⁻ ω,
      if twoSidedExitDownTime X (-x) ω <
          twoSidedExitUpTime X (a - x) ω then
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitDownTime X (-x) ω).toReal))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω))
      else 0 ∂P) =
        (∫⁻ _ : Ω, (0 : ℝ≥0∞) ∂P) := by
      apply lintegral_congr_ae
      filter_upwards [hNoCreep] with ω hnc
      rw [AvramDividend.Classical.chat04_lower_exit_scale_creeping_atom
        X q W hW a x ω]
      by_cases h : twoSidedExitDownTime X (-x) ω <
          twoSidedExitUpTime X (a - x) ω
      · simp only [if_pos h, if_neg (hnc h), mul_zero]
      · simp only [if_neg h]
    _ = 0 := lintegral_zero
