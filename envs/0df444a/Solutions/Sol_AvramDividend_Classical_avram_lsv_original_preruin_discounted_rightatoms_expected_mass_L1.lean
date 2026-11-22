-- Prove2me | solution 1 for AvramDividend.Classical.avram_lsv_original_preruin_discounted_rightatoms_expected_mass_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T16:09:48.819918+00:00
-- url     : https://prove2.me/submissions/bd6626b6-9696-4ff2-a3c9-4382fe28f5af

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_lsv_original_preruin_discounted_grid_rightatoms_runningSup_bound
import Theorems.Thm_AvramDividend_Classical_avram_f6_mixed_gaussian_true_fixed_horizon_runningSup_L1
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_measurable
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hσ : 0 < X.σ)
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
    Integrable A P ∧
      (∫ ω, A ω ∂P) ≤
        ∫ ω, x + runningSup X n ω ∂P := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let A : Ω → ℝ := fun ω =>
    ∑ i ∈ Finset.range m,
      if s i < ρ ω then
        Real.exp (-(q * (s i : ℝ))) *
          (rightLimit D (s i) ω - D (s i) ω)
      else 0
  have hρmeas : Measurable ρ :=
    measurable_coe_nnreal_ennreal_iff.mp hρstop.measurable'
  have hAm : Measurable A := by
    dsimp [A]
    apply Finset.measurable_sum
    intro i hi
    have hevent : MeasurableSet {ω : Ω | s i < ρ ω} :=
      measurableSet_lt measurable_const hρmeas
    have hgap : Measurable (fun ω =>
        rightLimit D (s i) ω - D (s i) ω) :=
      (dividendStrategy_rightLimit_measurable D hD (s i)).sub
        hD.2.2.2.measurable
    exact Measurable.ite hevent (measurable_const.mul hgap) measurable_const
  have hPoint (ω : Ω) :
      0 ≤ A ω ∧ A ω ≤ x + runningSup X n ω := by
    constructor
    · dsimp [A]
      apply Finset.sum_nonneg
      intro i hi
      by_cases h : s i < ρ ω
      · simp only [if_pos h]
        exact mul_nonneg (Real.exp_nonneg _) (sub_nonneg.mpr
          (dividendStrategy_le_rightLimit D hD ω (s i)))
      · simp [h]
    · exact avram_lsv_original_preruin_discounted_grid_rightatoms_runningSup_bound
        X x hx D hD n ρ hρruin s hstrict m hbound q hq ω
  have hSupI : Integrable (fun ω => x + runningSup X n ω) P :=
    (integrable_const x).add
      (avram_f6_mixed_gaussian_true_fixed_horizon_runningSup_L1 X hσ n)
  have hUpperNonneg (ω : Ω) : 0 ≤ x + runningSup X n ω := by
    have hh : 0 ≤ runningSup X n ω := by
      obtain ⟨hMono,hPath⟩ := runningSup_monotone_and_path_le X ω
      have h0 := hPath 0
      rw [X.X_zero ω] at h0
      exact h0.trans (hMono (show (0 : ℝ≥0) ≤ n from zero_le))
    exact add_nonneg hx hh
  have hAI : Integrable A P := by
    apply hSupI.mono' hAm.aestronglyMeasurable
    exact ae_of_all _ (fun ω => by
      have h := hPoint ω
      simpa only [Real.norm_eq_abs, abs_of_nonneg h.1,
        abs_of_nonneg (hUpperNonneg ω)] using h.2)
  refine ⟨hAI, ?_⟩
  exact integral_mono_ae hAI hSupI
    (ae_of_all _ (fun ω => (hPoint ω).2))

