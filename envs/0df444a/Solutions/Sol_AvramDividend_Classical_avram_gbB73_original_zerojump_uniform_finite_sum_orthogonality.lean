-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB73_original_zerojump_uniform_finite_sum_orthogonality
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T16:26:52.212215+00:00
-- url     : https://prove2.me/submissions/64fd10ae-523c-4ae3-8900-9ec067a09206

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_weighted_true_increment_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_gaussian_finite_predictable_grid_exact_L2_isometry
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (n N : ℕ) (hn : 0 < n) (hN : 0 < N)
    (H : ℕ → Ω → ℝ)
    (hAdapt : ∀ i : ℕ,
      Measurable[𝓕.rightCont
        ((i : ℝ≥0) * ((n : ℝ≥0) / (N : ℝ≥0)))] (H i))
    (hBound : ∃ B : ℝ, 0 ≤ B ∧ ∀ i ω, |H i ω| ≤ B) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / (N : ℝ≥0)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let L : Ω → ℝ := fun ω =>
      (Finset.range N).sum (fun i =>
        H i ω * (X.X (s i + Δ) ω - X.X (s i) ω -
          (Δ : ℝ) * X.c))
    (∫ ω, (L ω) ^ 2 ∂P) =
      (Finset.range N).sum (fun i =>
        ∫ ω, (H i ω * (X.X (s i + Δ) ω -
          X.X (s i) ω - (Δ : ℝ) * X.c)) ^ 2 ∂P) := by
  intro Δ s L
  have hstep : ∀ i : ℕ, s i + Δ = s (i + 1) := by
    intro i
    dsimp [s]
    push_cast
    ring
  have hmono : Monotone s := by
    intro i j hij
    dsimp [s]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) (by positivity)
  have hst : ∀ i ∈ Finset.range N, s i ≤ s i + Δ := by
    intro i hi
    exact le_add_of_nonneg_right (by positivity)
  have hsep : ∀ i ∈ Finset.range N, ∀ j ∈ Finset.range N,
      i ≠ j → s i + Δ ≤ s j ∨ s j + Δ ≤ s i := by
    intro i hi j hj hij
    rcases lt_or_gt_of_ne hij with hij | hji
    · left
      calc
        s i + Δ = s (i + 1) := hstep i
        _ ≤ s j := hmono (Nat.succ_le_iff.mpr hij)
    · right
      calc
        s j + Δ = s (j + 1) := hstep j
        _ ≤ s i := hmono (Nat.succ_le_iff.mpr hji)
  have hown : ∀ i ∈ Finset.range N,
      Measurable[𝓕.rightCont (s i)] (H i) := by
    intro i hi
    simpa only [s, Δ] using hAdapt i
  have hpair : ∀ i ∈ Finset.range N, ∀ j ∈ Finset.range N,
      s i + Δ ≤ s j →
      Measurable[𝓕.rightCont (s j)] (H i) := by
    intro i hi j hj hij
    have his := hown i hi
    exact his.mono (𝓕.rightCont.mono (le_trans (hst i hi) hij)) le_rfl
  obtain ⟨B, hB, hBnd⟩ := hBound
  have hLp : ∀ i ∈ Finset.range N,
      MemLp (fun ω => H i ω * (X.X (s i + Δ) ω -
        X.X (s i) ω - (((s i + Δ : ℝ≥0) : ℝ) - (s i : ℝ)) * X.c)) 2 P := by
    intro i hi
    have hGlobal : Measurable (H i) := by
      exact (hown i hi).mono (𝓕.rightCont.le _) le_rfl
    have hStop : IsStoppingTime 𝓕.rightCont
        (fun ω : Ω => ((s i : ℝ≥0) : WithTop ℝ≥0)) :=
      isStoppingTime_const 𝓕.rightCont (s i)
    have hLp' := avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_weighted_true_increment_MemLp_two
      X hν (fun _ : Ω => s i) hStop (s i)
      (by intro ω; exact le_refl _) Δ (H i) hGlobal.stronglyMeasurable
      B hB (hBnd i)
    simpa only [NNReal.coe_add, add_sub_cancel_left] using hLp'
  have hIso := avram_wave7_05_original_gaussian_finite_predictable_grid_exact_L2_isometry
    X hν (Finset.range N) s (fun i => s i + Δ) H
    hst hsep hown hpair hLp
  simpa only [L, s, Δ, NNReal.coe_add, add_sub_cancel_left] using hIso.2.2
