-- Prove2me | solution 9 for AvramDividend.Classical.vcstar_unrestricted_upper_bound_of_generator
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T13:26:38.805174+00:00
-- url     : https://prove2.me/submissions/6ec55b71-bbe7-4134-94bf-f1fd8409e056
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
-- Sweep16 immutable original unrestricted value adapter retry, 5 Nov 2026.
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_vcstar_unrestricted_verification_regularity
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_all_positive_of_generator
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
  obtain ⟨hcont, hw0, hwneg, hsmooth⟩ :=
    vcstar_unrestricted_verification_regularity X hX q hq W hW hc h_smooth
  have hw_smooth :
      (¬ X.BoundedVariation → ContDiffOn ℝ 2 (vcstar W)
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < (⊤ : ℝ≥0∞)}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 (vcstar W)
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < (⊤ : ℝ≥0∞)}) := by
    constructor
    · intro hBV
      exact (hsmooth.1 hBV).mono (by intro y hy; exact hy.1)
    · intro hBV
      exact (hsmooth.2 hBV).mono (by intro y hy; exact hy.1)
  have hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < (⊤ : ℝ≥0∞) →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
          (1 - deriv (vcstar W) y) = 0 := by
    intro y hy _
    exact vcstar_hjb_all_positive_of_generator X hX q hq W hW hc h_smooth hgen y hy
  have hVerify := local_verification X hX q hq (vcstar W) (⊤ : ℝ≥0∞)
    (by simp) hcont hw0 hwneg hw_smooth hw_hjb
  exact hVerify.2 rfl
