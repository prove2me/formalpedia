-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB81_original_mixed_cells_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T17:33:37.845575+00:00
-- url     : https://prove2.me/submissions/4d3a1920-db52-4d42-9bef-c6ac135cea27

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_gaussian_disjoint_predictable_cross_expectation_zero
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
    ∀ i j : ℕ, i ≠ j →
      (∫ ω, (H i ω * Z i ω) * (J j ω * Z j ω) ∂P) = 0 := by
  intro Δ s Z i j hij
  have hstep : ∀ k : ℕ, s k + Δ = s (k + 1) := by
    intro k
    dsimp [s]
    push_cast
    ring
  have hmono : Monotone s := by
    intro a b hab
    dsimp [s]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hab) (by positivity)
  have hLp (W : ℕ → Ω → ℝ)
      (hAdapt : ∀ k, Measurable[𝓕.rightCont (s k)] (W k))
      (hBound : ∃ C : ℝ, 0 ≤ C ∧ ∀ k ω, |W k ω| ≤ C)
      (k : ℕ) : MemLp (fun ω => W k ω * Z k ω) 2 P := by
    obtain ⟨C, hC, hCbd⟩ := hBound
    have hGlobal : Measurable (W k) :=
      (hAdapt k).mono (𝓕.rightCont.le _) le_rfl
    have hStop : IsStoppingTime 𝓕.rightCont
        (fun ω : Ω => ((s k : ℝ≥0) : WithTop ℝ≥0)) :=
      isStoppingTime_const 𝓕.rightCont (s k)
    have hh := avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_weighted_true_increment_MemLp_two
      X hν (fun _ : Ω => s k) hStop (s k)
      (by intro ω; exact le_refl _) Δ (W k) hGlobal.stronglyMeasurable
      C hC (hCbd k)
    simpa only [Z, NNReal.coe_add, add_sub_cancel_left] using hh
  have hAdaptH : ∀ k, Measurable[𝓕.rightCont (s k)] (H k) := by
    intro k
    simpa only [s, Δ] using hHAdapt k
  have hAdaptJ : ∀ k, Measurable[𝓕.rightCont (s k)] (J k) := by
    intro k
    simpa only [s, Δ] using hJAdapt k
  have hLpH := hLp H hAdaptH hHBound i
  have hLpJ := hLp J hAdaptJ hJBound j
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hsep : s i + Δ ≤ s j := by
      calc
        s i + Δ = s (i + 1) := hstep i
        _ ≤ s j := hmono (Nat.succ_le_iff.mpr hlt)
    have hHlater : Measurable[𝓕.rightCont (s j)] (H i) :=
      (hAdaptH i).mono
        (𝓕.rightCont.mono (le_trans (le_add_of_nonneg_right (by positivity)) hsep)) le_rfl
    have hh := avram_wave7_05_original_gaussian_disjoint_predictable_cross_expectation_zero
      X hν (s i) (s i + Δ) (s j) (s j + Δ)
      (le_add_of_nonneg_right (by positivity)) hsep
      (le_add_of_nonneg_right (by positivity)) (H i) (J j)
      hHlater (hAdaptJ j)
      (by simpa only [Z, NNReal.coe_add, add_sub_cancel_left] using hLpH)
      (by simpa only [Z, NNReal.coe_add, add_sub_cancel_left] using hLpJ)
    simpa only [Pi.mul_apply, Z, NNReal.coe_add, add_sub_cancel_left] using hh.2
  · have hsep : s j + Δ ≤ s i := by
      calc
        s j + Δ = s (j + 1) := hstep j
        _ ≤ s i := hmono (Nat.succ_le_iff.mpr hgt)
    have hJlater : Measurable[𝓕.rightCont (s i)] (J j) :=
      (hAdaptJ j).mono
        (𝓕.rightCont.mono (le_trans (le_add_of_nonneg_right (by positivity)) hsep)) le_rfl
    have hh := avram_wave7_05_original_gaussian_disjoint_predictable_cross_expectation_zero
      X hν (s j) (s j + Δ) (s i) (s i + Δ)
      (le_add_of_nonneg_right (by positivity)) hsep
      (le_add_of_nonneg_right (by positivity)) (J j) (H i)
      hJlater (hAdaptH i)
      (by simpa only [Z, NNReal.coe_add, add_sub_cancel_left] using hLpJ)
      (by simpa only [Z, NNReal.coe_add, add_sub_cancel_left] using hLpH)
    calc
      (∫ ω, (H i ω * Z i ω) * (J j ω * Z j ω) ∂P) =
        (∫ ω, (J j ω * Z j ω) * (H i ω * Z i ω) ∂P) := by
          apply integral_congr_ae
          filter_upwards with ω
          ring
      _ = 0 := by
          simpa only [Pi.mul_apply, Z, NNReal.coe_add, add_sub_cancel_left] using hh.2
