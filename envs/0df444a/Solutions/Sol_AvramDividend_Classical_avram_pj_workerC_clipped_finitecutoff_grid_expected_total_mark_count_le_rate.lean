-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_clipped_finitecutoff_grid_expected_total_mark_count_le_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T08:36:07.799447+00:00
-- url     : https://prove2.me/submissions/ba80fd2d-b1fa-4e19-bd15-4bb729467346

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_physical_stopped_grid_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_uniform_physical_clock_endpoints_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_run1640_original_marked_count_grid_telescoping
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_zero_origin_separated_negative_borel_levy_rate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ρ : Ω → ℝ≥0) (n m : ℕ)
    (hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0))
    (B : Set ℝ) (hB : MeasurableSet B)
    (ε : ℝ) (hε : 0 < ε) (hBsep : B ⊆ Iic (-ε)) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let u : Ω → ℕ → ℝ≥0 := fun ω i =>
      min (((min i (m + 1) : ℕ) : ℝ≥0) * Δ) (ρ ω)
    let J : Ω → Set ℝ≥0 → ℝ≥0∞ := fun ω I =>
      ((Measure.count.restrict {t : ℝ≥0 |
        0 < t ∧ X.X t ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t,
          X.X t ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)))
        (I ×ˢ B)
    (∫⁻ ω, (∑ i ∈ Finset.range (m + 1),
      J ω (Ioc (u ω i) (u ω (i+1)))) ∂P) ≤
    ((n : ℝ≥0) : ℝ≥0∞) * X.ν B := by
  intro Δ u J
  have hCells (ω : Ω) :
      (∑ i ∈ Finset.range (m+1),
        J ω (Ioc (u ω i) (u ω (i+1)))) =
      J ω (Ioc 0 (ρ ω)) := by
    have hm : Monotone (u ω) := by
      simpa [u, Δ] using
        (AvramDividend.Classical.avram_p3_2_physical_stopped_grid_monotone
          (n : ℝ≥0) (ρ ω) m)
    have hZero : u ω 0 = 0 := by simp [u, Δ]
    have hEnd : u ω (m+1) = ρ ω := by
      have ht :=
        (AvramDividend.Classical.avram_p3_grid3_uniform_physical_clock_endpoints_monotone
          (n : ℝ≥0) m).2.1
      change min (((min (m+1) (m+1) : ℕ) : ℝ≥0) * Δ) (ρ ω) = ρ ω
      have hT : (((min (m+1) (m+1) : ℕ) : ℝ≥0) * Δ) =
          (n : ℝ≥0) := by simpa [Δ] using ht
      rw [hT]
      exact min_eq_right (hρbound ω)
    have hPart :=
      AvramDividend.Classical.avram_p4_s3_run1640_original_marked_count_grid_telescoping
        X ω (u ω) (fun i => hm (Nat.le_succ i)) hZero B hB (m+1)
    simpa only [hEnd] using hPart
  have hMon (ω : Ω) :
      J ω (Ioc 0 (ρ ω)) ≤ J ω (Ioc 0 (n : ℝ≥0)) := by
    apply measure_mono
    intro p hp
    obtain ⟨ht, hz⟩ := hp
    exact ⟨⟨ht.1, ht.2.trans (hρbound ω)⟩, hz⟩
  calc
    (∫⁻ ω, (∑ i ∈ Finset.range (m+1),
      J ω (Ioc (u ω i) (u ω (i+1)))) ∂P) =
      (∫⁻ ω, J ω (Ioc 0 (ρ ω)) ∂P) := by
        apply lintegral_congr_ae
        filter_upwards [] with ω
        exact hCells ω
    _ ≤ (∫⁻ ω, J ω (Ioc 0 (n : ℝ≥0)) ∂P) :=
      lintegral_mono hMon
    _ = ((n : ℝ≥0) : ℝ≥0∞) * X.ν B :=
      AvramDividend.Classical.avram_wave7_01_original_zero_origin_separated_negative_borel_levy_rate
        X (n : ℝ≥0) B hB ε hε hBsep

