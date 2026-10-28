-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_contDiffOn_one_of_boundedVariation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T22:32:45.068503+00:00
-- url     : https://prove2.me/submissions/4c75b97b-5b2d-4c15-a5f0-f7beccc7b10f

import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_bv_absolutely_continuous_levy
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation) :
    ContDiffOn ℝ 1 W (Ioi 0) := by
  have hcondition : X.Condition33 := hX.2.2
  change (0 < X.σ ∨
    (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν) = ⊤ ∨
    X.ν ≪ volume) at hcondition
  have hac : X.ν ≪ volume := by
    rcases hcondition with hσ | hInfinite | hac
    · have hzero : X.σ = 0 := hBV.1
      rw [hzero] at hσ
      exact False.elim (lt_irrefl (0 : ℝ) hσ)
    · have hfinite :
          (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν) < ⊤ :=
        hBV.2
      rw [hInfinite] at hfinite
      exact False.elim (lt_irrefl (⊤ : ℝ≥0∞) hfinite)
    · exact hac
  exact scaleFunction_contDiff_one_of_bv_absolutely_continuous_levy
    X hX q hq W hW hBV hac
