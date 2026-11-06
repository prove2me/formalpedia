-- Prove2me | solution 7 for AvramDividend.Classical.vcstar_unrestricted_upper_bound_of_generator
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T10:00:20.041096+00:00
-- url     : https://prove2.me/submissions/6bda96d3-a6b7-4028-b221-c9d47f92ec37
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_all_positive_of_generator
import Theorems.Thm_AvramDividend_Classical_vcstar_unrestricted_verification_regularity
import Theorems.Thm_AvramDividend_Classical_local_verification

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0))
    (hgen : ∀ y : ℝ, (cstar W).toReal < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        X.generator (vcstar W) y - q * vcstar W y ≤ 0) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunction X q x ≤ ENNReal.ofReal (vcstar W x) := by
  obtain ⟨hcont, hzero, hneg, hregular⟩ :=
    vcstar_unrestricted_verification_regularity X hX q hq W hW hc h_smooth
  have hstrip :
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < (⊤ : ℝ≥0∞)} = Ioi (0 : ℝ) := by
    ext y
    simp
  have hregular' :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 (vcstar W) {y : ℝ | 0 < y ∧ ENNReal.ofReal y < (⊤ : ℝ≥0∞)}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 (vcstar W) {y : ℝ | 0 < y ∧ ENNReal.ofReal y < (⊤ : ℝ≥0∞)}) := by
    simpa only [hstrip] using hregular
  have hhjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < (⊤ : ℝ≥0∞) →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
            (1 - deriv (vcstar W) y) = 0 := by
    intro y hy _
    exact vcstar_hjb_all_positive_of_generator X hX q hq W hW hc h_smooth hgen y hy
  exact (local_verification X hX q hq (vcstar W) (⊤ : ℝ≥0∞)
    (by simp) hcont hzero hneg hregular' hhjb).2 rfl
