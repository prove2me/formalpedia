-- Prove2me | solution 7 for AvramDividend.Classical.barrier_cstar_verification_upper_bounds
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:18:26.957792+00:00
-- url     : https://prove2.me/submissions/ef945513-5fdd-4b39-8186-9c9cae31c2c1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrier_cstar_capped_value_upper_bound_of_positive_cstar
import Theorems.Thm_AvramDividend_Classical_zero_cap_value_at_zero_upper_bound
import Theorems.Thm_AvramDividend_Classical_barrier_zero_boundary_value_nonneg
import Theorems.Thm_AvramDividend_Classical_zero_cap_value_upper_bound_of_zero_bound
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_all_positive_of_generator
import Theorems.Thm_AvramDividend_Classical_vcstar_unrestricted_verification_regularity
import Theorems.Thm_AvramDividend_Classical_local_verification_uniform_strategy_bound
import Theorems.Thm_AvramDividend_Classical_local_verification_from_uniform_strategy_bound

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
  · intro x hx
    by_cases hcpos : 0 < cstar W
    · exact barrier_cstar_capped_value_upper_bound_of_positive_cstar
        X hX q hq W hW hc hcpos h_smooth x hx
    · have hc0 : cstar W = 0 := by
        have hzero_le : (0 : ℝ≥0∞) ≤ cstar W := bot_le
        exact le_antisymm (le_of_not_gt hcpos) hzero_le
      have hboundary :=
        zero_cap_value_at_zero_upper_bound X hX q hq W hW
      have hval := (barrier_zero_boundary_value_nonneg X hX q hq W hW).1
      have hAll :=
        zero_cap_value_upper_bound_of_zero_bound X q W hboundary hval x hx
      simpa [vcstar, hc0] using hAll
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
      exact vcstar_hjb_all_positive_of_generator X hX q hq W hW hc h_smooth hgen y hy
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
