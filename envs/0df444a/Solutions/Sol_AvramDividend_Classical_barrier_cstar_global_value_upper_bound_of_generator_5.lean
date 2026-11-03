-- Prove2me | solution 5 for AvramDividend.Classical.barrier_cstar_global_value_upper_bound_of_generator
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:28:51.291209+00:00
-- url     : https://prove2.me/submissions/a0ad4067-ff5c-4e2a-a5df-5e85bf88cf19
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_vcstar_unrestricted_verification_regularity
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_all_positive_of_generator
import Theorems.Thm_AvramDividend_Classical_local_verification_from_uniform_strategy_bound
import Theorems.Thm_AvramDividend_Classical_admissible_cap_dividendValue_le_bounded_variation
import Theorems.Thm_AvramDividend_Classical_admissible_cap_dividendValue_le_unbounded_variation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Unrestricted upper bound directly from the genuine BV and UBV strategy bounds. -/
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
  have hsubset :
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < (⊤ : ℝ≥0∞)} ⊆ Ioi (0 : ℝ) := by
    intro y hy
    exact hy.1
  have hsmoothTop :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 (vcstar W)
          {y : ℝ | 0 < y ∧ ENNReal.ofReal y < (⊤ : ℝ≥0∞)}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 (vcstar W)
          {y : ℝ | 0 < y ∧ ENNReal.ofReal y < (⊤ : ℝ≥0∞)}) :=
    ⟨fun h => (hsmooth.1 h).mono hsubset,
     fun h => (hsmooth.2 h).mono hsubset⟩
  have hhjbTop :
      ∀ y : ℝ, 0 < y → ENNReal.ofReal y < (⊤ : ℝ≥0∞) →
        X.GeneratorIntegrable (vcstar W) y ∧
          max (X.generator (vcstar W) y - q * vcstar W y)
              (1 - deriv (vcstar W) y) = 0 := by
    intro y hy _
    exact vcstar_hjb_all_positive_of_generator
      X hX q hq W hW hc h_smooth hgen y hy
  have hstrategy : ∀ x : ℝ, 0 ≤ x →
      ENNReal.ofReal x ≤ (⊤ : ℝ≥0∞) →
      ∀ D : ℝ≥0 → Ω → ℝ, IsAdmissibleLe X x (⊤ : ℝ≥0∞) D →
        dividendValue X q x D ≤ ENNReal.ofReal (vcstar W x) := by
    intro x hx hxc D hD
    by_cases hBV : X.BoundedVariation
    · exact admissible_cap_dividendValue_le_bounded_variation
        X hX hBV q hq (vcstar W) (⊤ : ℝ≥0∞) ENNReal.zero_lt_top
        hcont hw0 hwneg (hsmoothTop.2 hBV) hhjbTop
        x hx hxc D hD
    · exact admissible_cap_dividendValue_le_unbounded_variation
        X hX hBV q hq (vcstar W) (⊤ : ℝ≥0∞) ENNReal.zero_lt_top
        hcont hw0 hwneg (hsmoothTop.1 hBV) hhjbTop
        x hx hxc D hD
  exact (local_verification_from_uniform_strategy_bound
    X q (vcstar W) (⊤ : ℝ≥0∞) hstrategy).2 rfl
