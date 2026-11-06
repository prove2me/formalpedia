-- Prove2me | solution 8 for AvramDividend.Classical.barrier_cstar_verification_upper_bounds
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:56:06.940623+00:00
-- url     : https://prove2.me/submissions/927232fa-28a0-47dd-8998-5dc41b22533a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_sweep17_cstar_inside_cap_bound_extends_all_capital
import Theorems.Thm_AvramDividend_Classical_avram_sweep17_vcstar_nonnegative_all_capital
import Theorems.Thm_AvramDividend_Classical_avram_sweep17_vcstar_positive_cap_interior_HJB
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_vcstar_zero_cstar_capped_upper
import Theorems.Thm_AvramDividend_Classical_vcstar_local_verification_regular_of_positive_cstar
import Theorems.Thm_AvramDividend_Classical_local_verification
import Theorems.Thm_AvramDividend_Classical_vcstar_unrestricted_verification_regularity
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_all_positive_of_generator
import Theorems.Thm_AvramDividend_Classical_local_verification_uniform_strategy_bound
import Theorems.Thm_AvramDividend_Classical_local_verification_from_uniform_strategy_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
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
  · intro x hx
    by_cases hcpos : 0 < cstar W
    · obtain ⟨hcont, hzero, hneg, hsmooth⟩ :=
        vcstar_local_verification_regular_of_positive_cstar
          X hX q hq W hW hc hcpos h_smooth
      have hhjb :=
        avram_sweep17_vcstar_positive_cap_interior_HJB
          X hX q hq W hW hc hcpos h_smooth
      have hInside :=
        (local_verification X hX q hq (vcstar W) (cstar W)
          hcpos hcont hzero hneg hsmooth hhjb).1
      have hnonneg :=
        avram_sweep17_vcstar_nonnegative_all_capital
          X hX q hq W hW hc h_smooth
          (cstar W).toReal ENNReal.toReal_nonneg
      exact avram_sweep17_cstar_inside_cap_bound_extends_all_capital
        X q W hc hnonneg hInside x hx
    · have hc0 : cstar W = 0 := by
        have hzero_le : (0 : ℝ≥0∞) ≤ cstar W := bot_le
        exact le_antisymm (le_of_not_gt hcpos) hzero_le
      exact avram_sweep16_original_vcstar_zero_cstar_capped_upper
        X hX q hq W hW hc0 x hx
  · intro hgen
    obtain ⟨hcont, hzero, hneg, hregSource⟩ :=
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
      simpa only [hstrip] using hregSource
    have hhjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < (⊤ : ℝ≥0∞) →
        X.GeneratorIntegrable (vcstar W) y ∧
          max (X.generator (vcstar W) y - q * vcstar W y)
              (1 - deriv (vcstar W) y) = 0 := by
      intro y hy _
      exact vcstar_hjb_all_positive_of_generator
        X hX q hq W hW hc h_smooth hgen y hy
    have hUniform : ∀ x : ℝ, 0 ≤ x →
        ENNReal.ofReal x ≤ (⊤ : ℝ≥0∞) →
        ∀ D : ℝ≥0 → Ω → ℝ, IsAdmissibleLe X x (⊤ : ℝ≥0∞) D →
          dividendValue X q x D ≤ ENNReal.ofReal (vcstar W x) := by
      intro x hx hxC D hD
      exact local_verification_uniform_strategy_bound X hX q hq
        (vcstar W) (⊤ : ℝ≥0∞) (by simp) hcont hzero hneg
        hregular' hhjb x hx hxC D hD
    exact (local_verification_from_uniform_strategy_bound
      X q (vcstar W) (⊤ : ℝ≥0∞) hUniform).2 rfl
