-- Prove2me | solution 6 for AvramDividend.Classical.barrier_cstar_verification_upper_bounds
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T11:54:59.219734+00:00
-- url     : https://prove2.me/submissions/6c198800-2e3f-4b1e-8afa-e78e1fffe253
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_vcstar_capped_upper_bound_all_capital
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_all_positive_of_generator
import Theorems.Thm_AvramDividend_Classical_vcstar_unrestricted_verification_regularity
import Theorems.Thm_AvramDividend_Classical_local_verification

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    (∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q (cstar W) x ≤ ENNReal.ofReal (vcstar W x)) ∧
    ((∀ y : ℝ, (cstar W).toReal < y →
       X.GeneratorIntegrable (vcstar W) y ∧
         X.generator (vcstar W) y - q * vcstar W y ≤ 0) →
      ∀ x : ℝ, 0 ≤ x →
        valueFunction X q x ≤ ENNReal.ofReal (vcstar W x)) := by
  constructor
  · exact vcstar_capped_upper_bound_all_capital X hX q hq W hW hc h_smooth
  · intro hgen
    obtain ⟨hcont, hzero, hneg, hregular⟩ :=
      vcstar_unrestricted_verification_regularity X hX q hq W hW hc h_smooth
    have hstrip :
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < (⊤ : ℝ≥0∞)} = Ioi (0 : ℝ) := by
      ext y
      simp
    have hregular' :
        (¬ X.BoundedVariation →
          ContDiffOn ℝ 2 (vcstar W)
            {y : ℝ | 0 < y ∧ ENNReal.ofReal y < (⊤ : ℝ≥0∞)}) ∧
        (X.BoundedVariation →
          ContDiffOn ℝ 1 (vcstar W)
            {y : ℝ | 0 < y ∧ ENNReal.ofReal y < (⊤ : ℝ≥0∞)}) := by
      simpa only [hstrip] using hregular
    have hhjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < (⊤ : ℝ≥0∞) →
        X.GeneratorIntegrable (vcstar W) y ∧
          max (X.generator (vcstar W) y - q * vcstar W y)
              (1 - deriv (vcstar W) y) = 0 := by
      intro y hy _
      exact vcstar_hjb_all_positive_of_generator X hX q hq W hW hc h_smooth hgen y hy
    exact (local_verification X hX q hq (vcstar W) (⊤ : ℝ≥0∞)
      (by simp) hcont hzero hneg hregular' hhjb).2 rfl
