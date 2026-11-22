-- Prove2me | solution 1 for AvramDividend.Classical.avram_lsv_original_preruin_discounted_rightatoms_square_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T16:57:00.076818+00:00
-- url     : https://prove2.me/submissions/015e3e3e-5260-4e7c-afc1-353996106e96

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_lsv_original_preruin_discounted_grid_rightatoms_runningSup_bound
import Theorems.Thm_AvramDividend_Classical_avram_lsv_original_preruin_discounted_rightatoms_expected_mass_L1
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_unboundedvariation_finitehorizon_runningSup_square_integrable
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (hσ : 0 < X.σ)
    (x : ℝ) (hx : 0 ≤ x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (n : ℝ≥0) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρruin : ∀ ω, (ρ ω : ℝ≥0∞) ≤ ruinTime X x D ω)
    (s : ℕ → ℝ≥0) (hstrict : ∀ i, s i < s (i + 1))
    (m : ℕ) (hbound : ∀ i ∈ Finset.range m, s i ≤ n)
    (q : ℝ) (hq : 0 ≤ q) :
    let A : Ω → ℝ := fun ω =>
      ∑ i ∈ Finset.range m,
        if s i < ρ ω then
          Real.exp (-(q * (s i : ℝ))) *
            (rightLimit D (s i) ω - D (s i) ω)
        else 0
    Integrable (fun ω => (A ω)^2) P ∧
      (∫ ω, (A ω)^2 ∂P) ≤
        ∫ ω, 2*x^2 + 2*(runningSup X n ω)^2 ∂P := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let A : Ω → ℝ := fun ω =>
    ∑ i ∈ Finset.range m,
      if s i < ρ ω then
        Real.exp (-(q * (s i : ℝ))) *
          (rightLimit D (s i) ω - D (s i) ω)
      else 0
  have hAI : Integrable A P :=
    (avram_lsv_original_preruin_discounted_rightatoms_expected_mass_L1
      X hσ x hx D hD n ρ hρstop hρruin
      s hstrict m hbound q hq).1
  have hSI : Integrable (fun ω => 2*x^2 + 2*(runningSup X n ω)^2) P :=
    (integrable_const (2*x^2)).add
      ((avram_pj_original_unboundedvariation_finitehorizon_runningSup_square_integrable
        X hBV n).const_mul 2)
  have hNonneg (ω : Ω) : 0 ≤ A ω := by
    dsimp [A]
    apply Finset.sum_nonneg
    intro i hi
    by_cases h : s i < ρ ω
    · simp only [if_pos h]
      exact mul_nonneg (Real.exp_nonneg _) (sub_nonneg.mpr
        (dividendStrategy_le_rightLimit D hD ω (s i)))
    · simp [h]
  have hBound (ω : Ω) : A ω ≤ x + runningSup X n ω :=
    avram_lsv_original_preruin_discounted_grid_rightatoms_runningSup_bound
      X x hx D hD n ρ hρruin s hstrict m hbound q hq ω
  have hSquarePoint (ω : Ω) :
      (A ω)^2 ≤ 2*x^2 + 2*(runningSup X n ω)^2 := by
    have h0 := hNonneg ω
    have hle := hBound ω
    have hU : 0 ≤ x + runningSup X n ω := h0.trans hle
    have hprod := mul_nonneg (sub_nonneg.mpr hle) (add_nonneg hU h0)
    have hsq := sq_nonneg (x - runningSup X n ω)
    nlinarith
  have hSqI : Integrable (fun ω => (A ω)^2) P := by
    apply hSI.mono' (AEStronglyMeasurable.pow hAI.aestronglyMeasurable 2)
    exact ae_of_all _ (fun ω => by
      have hmaj : 0 ≤ 2*x^2 + 2*(runningSup X n ω)^2 := by positivity
      change |(A ω)^2| ≤ 2*x^2 + 2*(runningSup X n ω)^2
      simpa only [abs_of_nonneg (sq_nonneg (A ω))]
        using hSquarePoint ω)
  exact ⟨hSqI, integral_mono_ae hSqI hSI
    (ae_of_all _ (fun ω => hSquarePoint ω))⟩

