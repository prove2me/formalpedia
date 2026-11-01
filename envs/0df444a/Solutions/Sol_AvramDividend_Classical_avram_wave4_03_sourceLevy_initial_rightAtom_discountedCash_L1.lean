-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_sourceLevy_initial_rightAtom_discountedCash_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T19:08:55.693319+00:00
-- url     : https://prove2.me/submissions/abd0eb91-d467-4058-b15f-4697189b6d42

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_adapted_rightCont
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_exponential_control_loss_dominates_discounted_dividend_increment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- Actual source control's initial right-payment atom is bounded and L1. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    Integrable (fun ω => θ * Real.exp (-(θ * rightLimit D 0 ω)) *
      rightLimit D 0 ω) P ∧
    ∀ ω, 0 ≤ θ * Real.exp (-(θ * rightLimit D 0 ω)) *
      rightLimit D 0 ω ∧
      θ * Real.exp (-(θ * rightLimit D 0 ω)) *
        rightLimit D 0 ω ≤ 1 := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hD0 (ω : Ω) : 0 ≤ rightLimit D 0 ω := by
    simpa only [hD.1 ω] using
      dividendStrategy_le_rightLimit D hD ω (0 : ℝ≥0)
  have hfirst (ω : Ω) :
      θ * Real.exp (-(θ * rightLimit D 0 ω)) *
        rightLimit D 0 ω ≤
        1 - Real.exp (-(θ * rightLimit D 0 ω)) := by
    simpa using
      (avram_wave4_03_exponential_control_loss_dominates_discounted_dividend_increment
        θ 0 (rightLimit D 0 ω) hθ (hD0 ω))
  have hpos (ω : Ω) :
      0 ≤ θ * Real.exp (-(θ * rightLimit D 0 ω)) *
        rightLimit D 0 ω :=
    mul_nonneg (mul_nonneg hθ (Real.exp_pos _).le) (hD0 ω)
  have hbound (ω : Ω) :
      θ * Real.exp (-(θ * rightLimit D 0 ω)) *
        rightLimit D 0 ω ≤ 1 :=
    le_trans (hfirst ω) (sub_le_self 1 (Real.exp_pos _).le)
  have hmeas : Measurable (fun ω : Ω => θ *
      Real.exp (-(θ * rightLimit D 0 ω)) * rightLimit D 0 ω) := by
    have hm : Measurable (rightLimit D (0 : ℝ≥0)) :=
      (dividendStrategy_rightLimit_adapted_rightCont D hD 0).mono
        (𝓕.rightCont.le 0) le_rfl
    exact ((measurable_const.mul ((measurable_const.mul hm).neg.exp)).mul hm)
  refine ⟨?_, fun ω => ⟨hpos ω, hbound ω⟩⟩
  apply Integrable.of_bound hmeas.aestronglyMeasurable 1
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (hpos ω)]
  exact hbound ω
