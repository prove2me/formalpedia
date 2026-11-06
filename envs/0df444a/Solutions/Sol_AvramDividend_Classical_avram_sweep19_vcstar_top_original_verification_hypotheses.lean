-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep19_vcstar_top_original_verification_hypotheses
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:01:00.313357+00:00
-- url     : https://prove2.me/submissions/ab52515d-d224-476c-8a38-29ed3ea1fc2a

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_vcstar_unrestricted_verification_regularity
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_all_positive_of_generator
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0))
    (hgen : ∀ y : ℝ, (cstar W).toReal < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        X.generator (vcstar W) y - q * vcstar W y ≤ 0) :
    ContinuousOn (vcstar W) (Ici 0) ∧
    0 ≤ vcstar W 0 ∧
    (∀ y < 0, vcstar W y = 0) ∧
    ((¬ X.BoundedVariation →
      ContDiffOn ℝ 2 (vcstar W)
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < (⊤ : ℝ≥0∞)}) ∧
     (X.BoundedVariation →
      ContDiffOn ℝ 1 (vcstar W)
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < (⊤ : ℝ≥0∞)})) ∧
    (∀ y : ℝ, 0 < y → ENNReal.ofReal y < (⊤ : ℝ≥0∞) →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
          (1 - deriv (vcstar W) y) = 0) := by
  obtain ⟨hcont, hzero, hneg, hC2, hC1⟩ :=
    vcstar_unrestricted_verification_regularity
      X hX q hq W hW hc h_smooth
  have hRegion :
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < (⊤ : ℝ≥0∞)} = Ioi 0 := by
    ext y
    simp [Set.mem_setOf_eq, Set.mem_Ioi, ENNReal.ofReal_lt_top]
  have hSmooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 (vcstar W)
          {y : ℝ | 0 < y ∧ ENNReal.ofReal y < (⊤ : ℝ≥0∞)}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 (vcstar W)
          {y : ℝ | 0 < y ∧ ENNReal.ofReal y < (⊤ : ℝ≥0∞)}) := by
    constructor
    · intro hBV
      simpa only [hRegion] using hC2 hBV
    · intro hBV
      simpa only [hRegion] using hC1 hBV
  have hHJB : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < (⊤ : ℝ≥0∞) →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
          (1 - deriv (vcstar W) y) = 0 := by
    intro y hy _
    exact vcstar_hjb_all_positive_of_generator
      X hX q hq W hW hc h_smooth hgen y hy
  exact ⟨hcont, hzero, hneg, hSmooth, hHJB⟩
