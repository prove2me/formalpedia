-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB72_original_zerojump_uniform_single_cell_diagonal_variance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T16:25:57.083203+00:00
-- url     : https://prove2.me/submissions/adbd2842-8b62-4f0c-8b89-51e2e690f6f9

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_L2_isometry_eq
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
    ∀ i : ℕ,
      (∫ ω, (H i ω * (X.X (s i + Δ) ω -
        X.X (s i) ω - (Δ : ℝ) * X.c)) ^ 2 ∂P) =
      (∫ ω, (H i ω) ^ 2 ∂P) * ((Δ : ℝ) * X.σ ^ 2) := by
  intro Δ s i
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
  have hHist : Measurable[hStop.measurableSpace] (H i) := by
    have hle : 𝓕.rightCont t ≤ hStop.measurableSpace :=
      hStop.le_measurableSpace_of_const_le (by intro ω; exact le_refl _)
    have hMeas : Measurable[𝓕.rightCont t] (H i) := by
      simpa only [t, s, Δ] using hAdapt i
    exact hMeas.mono hle le_rfl
  have hGlobal : Measurable (H i) := by
    exact (hAdapt i).mono (𝓕.rightCont.le _) le_rfl
  have hCell :=
    avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_L2_isometry_eq
      X hν (fun _ : Ω => t) hτ t (by intro ω; exact le_refl t)
      Δ (H i) hHist hGlobal
  simpa only [t, s] using hCell
