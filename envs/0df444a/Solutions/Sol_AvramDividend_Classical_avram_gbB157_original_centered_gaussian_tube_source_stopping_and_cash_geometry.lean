-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB157_original_centered_gaussian_tube_source_stopping_and_cash_geometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T18:31:27.765983+00:00
-- url     : https://prove2.me/submissions/7572a7e7-fd02-45fb-b63f-2af5eff956ad

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB156_centered_short_Brownian_tube_implies_original_source_tube
import Theorems.Thm_AvramDividend_Classical_avram_gbB40_barrier_lower_hit_clock_equals_horizon_on_tube
import Theorems.Thm_AvramDividend_Classical_avram_gbB49_original_short_barrier_terminal_reserve_le_cap
import Theorems.Thm_AvramDividend_Classical_avram_gbB150_original_gaussian_centered_tube_terminal_reserve_near_cap
import Theorems.Thm_AvramDividend_Classical_avram_gbB149_original_gaussian_barrier_dividends_quantitative_drift_lower
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section
/-- Original centered Gaussian tube yields all stopped cash geometry. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (B : ℝ≥0 → ℝ)
    (hSource : ∀ s : ℝ≥0, s ≤ (1 / 1000 : ℝ≥0) →
      X.X s ω = B s + 2 * (s : ℝ))
    (hCentered : ∀ s : ℝ≥0, s ≤ (1 / 1000 : ℝ≥0) →
      |B s| ≤ (1 / 4000 : ℝ)) :
    sInf ((Icc (0 : ℝ≥0) (1 / 1000 : ℝ≥0) ∩
      (fun t : ℝ≥0 => -(riskProcess X (1 / 8 : ℝ)
        (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) t ω)) ⁻¹'
        Ici (-(5 / 44 : ℝ))) ∪ {(1 / 1000 : ℝ≥0)}) = (1 / 1000 : ℝ≥0) ∧
    (249 / 2000 : ℝ) ≤ riskProcess X (1 / 8 : ℝ) (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) (1 / 1000 : ℝ≥0) ω ∧
    riskProcess X (1 / 8 : ℝ) (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) (1 / 1000 : ℝ≥0) ω ≤ (1 / 8 : ℝ) ∧
    (173 / 100000 : ℝ) ≤ barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ) (99 / 100000 : ℝ≥0) ω := by
  have hTube :=
    avram_gbB156_centered_short_Brownian_tube_implies_original_source_tube
      X ω B hSource hCentered
  have hTpos : (0 : ℝ≥0) < (1 / 1000 : ℝ≥0) := by norm_num
  have hSpos : (0 : ℝ≥0) < (99 / 100000 : ℝ≥0) := by norm_num
  have hST : (99 / 100000 : ℝ≥0) < (1 / 1000 : ℝ≥0) := by norm_num
  have hDiv :=
    avram_gbB149_original_gaussian_barrier_dividends_quantitative_drift_lower
      X (99 / 100000 : ℝ≥0) hSpos ω (B (99 / 100000 : ℝ≥0))
      (hSource (99 / 100000 : ℝ≥0) (le_of_lt hST))
      (hCentered (99 / 100000 : ℝ≥0) (le_of_lt hST))
  have hYraw :=
    avram_gbB150_original_gaussian_centered_tube_terminal_reserve_near_cap
      X (1 / 1000 : ℝ≥0) hTpos ω B hSource hCentered
  have hYlower :
      (249 / 2000 : ℝ) ≤
        riskProcess X (1 / 8 : ℝ)
          (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ))
            (1 / 1000 : ℝ≥0) ω := by
    convert hYraw using 1 <;> norm_num
  refine ⟨
    avram_gbB40_barrier_lower_hit_clock_equals_horizon_on_tube
      X (1 / 1000 : ℝ≥0) ω hTube,
    hYlower,
    avram_gbB49_original_short_barrier_terminal_reserve_le_cap
      X (1 / 1000 : ℝ≥0) ω hTpos hTube, ?_⟩
  convert hDiv using 1 <;> norm_num
