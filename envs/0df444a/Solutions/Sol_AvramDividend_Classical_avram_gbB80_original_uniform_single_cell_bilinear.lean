-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB80_original_uniform_single_cell_bilinear
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T17:47:59.86289+00:00
-- url     : https://prove2.me/submissions/3498038c-ffd6-4e1b-9693-682acf207a99

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_stopped_gaussian_bilinear_exact_expected_covariance
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_weighted_true_increment_MemLp_two
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (n N : ℕ) (hn : 0 < n) (hN : 0 < N)
    (H J : ℕ → Ω → ℝ)
    (hHAdapt : ∀ (i : ℕ), Measurable[𝓕.rightCont ((i : ℝ≥0) * ((n : ℝ≥0) / (N : ℝ≥0)))] (H i))
    (hJAdapt : ∀ (i : ℕ), Measurable[𝓕.rightCont ((i : ℝ≥0) * ((n : ℝ≥0) / (N : ℝ≥0)))] (J i))
    (hHBound : ∃ B : ℝ, 0 ≤ B ∧ ∀ i ω, |H i ω| ≤ B)
    (hJBound : ∃ B : ℝ, 0 ≤ B ∧ ∀ i ω, |J i ω| ≤ B) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / (N : ℝ≥0)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let Z : ℕ → Ω → ℝ := fun i ω => X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c
    ∀ i : ℕ, (∫ ω, (H i ω * Z i ω) * (J i ω * Z i ω) ∂P) =
      ((Δ : ℝ) * X.σ ^ 2) * (∫ ω, H i ω * J i ω ∂P) := by
  intro Δ s Z i
  letI : IsProbabilityMeasure P := X.isProbability
  let t : ℝ≥0 := s i
  have hτ : ∀ z : ℝ≥0, MeasurableSet[𝓕.rightCont z]
      {ω : Ω | (fun _ : Ω => t) ω ≤ z} := by
    intro z
    by_cases hz : t ≤ z
    · simpa [hz] using (MeasurableSet.univ :
        MeasurableSet[𝓕.rightCont z] (Set.univ : Set Ω))
    · simpa [hz] using (MeasurableSet.empty :
        MeasurableSet[𝓕.rightCont z] (∅ : Set Ω))
  have hStop := isStoppingTime_withTop_of_le_events (fun _ : Ω => t) hτ
  have hHmeas : Measurable (H i) :=
    (hHAdapt i).mono (𝓕.rightCont.le _) le_rfl
  have hJmeas : Measurable (J i) :=
    (hJAdapt i).mono (𝓕.rightCont.le _) le_rfl
  have hHistH : Measurable[hStop.measurableSpace] (H i) := by
    have hle : 𝓕.rightCont t ≤ hStop.measurableSpace :=
      hStop.le_measurableSpace_of_const_le (by intro ω; exact le_refl _)
    have hm : Measurable[𝓕.rightCont t] (H i) := by
      simpa only [t, s, Δ] using hHAdapt i
    exact hm.mono hle le_rfl
  have hHistJ : Measurable[hStop.measurableSpace] (J i) := by
    have hle : 𝓕.rightCont t ≤ hStop.measurableSpace :=
      hStop.le_measurableSpace_of_const_le (by intro ω; exact le_refl _)
    have hm : Measurable[𝓕.rightCont t] (J i) := by
      simpa only [t, s, Δ] using hJAdapt i
    exact hm.mono hle le_rfl
  obtain ⟨BH, hBH, hHbd⟩ := hHBound
  obtain ⟨BJ, hBJ, hJbd⟩ := hJBound
  have hGH : Integrable (fun ω => H i ω * J i ω) P := by
    apply Integrable.of_bound (hHmeas.mul hJmeas).aestronglyMeasurable (BH * BJ)
    filter_upwards with ω
    simp only [Real.norm_eq_abs, Pi.mul_apply, abs_mul]
    calc
      |H i ω| * |J i ω| ≤ BH * |J i ω| :=
        mul_le_mul_of_nonneg_right (hHbd i ω) (abs_nonneg _)
      _ ≤ BH * BJ := mul_le_mul_of_nonneg_left (hJbd i ω) hBH
  have hLpH : MemLp (fun ω =>
      H i ω * (X.X (t + Δ) ω - X.X t ω - (Δ : ℝ) * X.c)) 2 P := by
    have hStopConst : IsStoppingTime 𝓕.rightCont
        (fun ω : Ω => ((t : ℝ≥0) : WithTop ℝ≥0)) :=
      isStoppingTime_const 𝓕.rightCont t
    exact avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_weighted_true_increment_MemLp_two
      X hν (fun _ : Ω => t) hStopConst t (by intro ω; exact le_refl _)
      Δ (H i) hHmeas.stronglyMeasurable BH hBH (hHbd i)
  have hLpJ : MemLp (fun ω =>
      J i ω * (X.X (t + Δ) ω - X.X t ω - (Δ : ℝ) * X.c)) 2 P := by
    have hStopConst : IsStoppingTime 𝓕.rightCont
        (fun ω : Ω => ((t : ℝ≥0) : WithTop ℝ≥0)) :=
      isStoppingTime_const 𝓕.rightCont t
    exact avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_weighted_true_increment_MemLp_two
      X hν (fun _ : Ω => t) hStopConst t (by intro ω; exact le_refl _)
      Δ (J i) hJmeas.stronglyMeasurable BJ hBJ (hJbd i)
  have hProd : Integrable (fun ω =>
      (H i ω * J i ω) *
        (X.X (t + Δ) ω - X.X t ω - (Δ : ℝ) * X.c) ^ 2) P := by
    convert hLpH.integrable_mul hLpJ using 1
    ext ω
    simp only [Pi.mul_apply]
    ring
  have hCell := avram_wave7_05_original_stopped_gaussian_bilinear_exact_expected_covariance
    X hν (fun _ : Ω => t) hτ t (by intro ω; exact le_refl _)
    Δ (H i) (J i) hHistH hHistJ hGH hProd
  simpa only [Pi.mul_apply, Z, s, t] using hCell.2
