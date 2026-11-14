-- Prove2me | solution 1 for AvramDividend.Classical.avram_a22_original_finiteactivity_raw_mark_cutoff_recovers_complete_physical_jump_series
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T21:09:07.215102+00:00
-- url     : https://prove2.me/submissions/bfa69a53-b9ba-40c5-a100-6d3322bcdbb7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_jump_tsum_finite_ae
import Theorems.Thm_AvramDividend_Classical_avram_a22_original_finiteactivity_actual_negative_marks_eventually_below_cutoff
import Theorems.Thm_AvramDividend_Classical_avram_a22_original_signed_jump_tsum_equals_negative_leftjump_magnitude_tsum
import Theorems.Thm_AvramDividend_Classical_avram_a22_original_largejump_raw_source_equals_physical_finite_mark_sum
import Theorems.Thm_AvramDividend_Classical_avram_a22_original_restored_compensator_smalljump_equals_physical_finite_mark_sum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators
noncomputable section

/-- Once every mark is below the genuine negative cutoff, large and small finite source bands partition the marks. -/
private theorem avram_a22_local_signed_band_partition
    (F : Finset ℝ≥0) (j : ℝ≥0 → ℝ) (n : ℕ)
    (hGap : ∀ u ∈ F, j u ≤ -(1 / ((n : ℝ) + 1))) :
    (∑ u ∈ F, if j u ≤ -1 then j u else 0) +
      (∑ u ∈ F, if -1 < j u ∧
        j u ≤ -(1 / ((n : ℝ) + 1)) then j u else 0) =
      ∑ u ∈ F, j u := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hl : j u ≤ -1
  · have hs : ¬ (-1 < j u ∧
      j u ≤ -(1 / ((n : ℝ) + 1))) :=
      fun h => (not_lt_of_ge hl) h.1
    simp only [if_pos hl, if_neg hs, add_zero]
  · have hs : -1 < j u ∧
        j u ≤ -(1 / ((n : ℝ) + 1)) :=
      ⟨lt_of_not_ge hl, hGap u hu⟩
    simpa only [if_neg hl, if_pos hs, zero_add]

/-- Recover all physical original negative jumps from original large marks and compensated finite small marks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω +
          avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω +
          (t : ℝ) * (∫ z in Ioc (-1 : ℝ)
             (-(1 / ((n : ℝ) + 1))), z ∂X.ν))
        atTop
        (𝓝 (-(∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0))) := by
  have hFin := avram_ubv_mixed12_original_jump_tsum_finite_ae X hFinite
  have hGap :=
    avram_a22_original_finiteactivity_actual_negative_marks_eventually_below_cutoff
      X hFinite
  filter_upwards [hFin, hGap] with ω hFω hGω
  intro t
  obtain ⟨F, hMem, hSum⟩ := hFω t
  obtain ⟨N, hN⟩ := hGω t
  let j : ℝ≥0 → ℝ := fun u =>
    X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
  have hSigned : (∑ u ∈ F, j u) =
      -(∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0) :=
    hSum.symm.trans
      (avram_a22_original_signed_jump_tsum_equals_negative_leftjump_magnitude_tsum X ω t)
  refine (tendsto_congr' ?_).2 tendsto_const_nhds
  filter_upwards [eventually_ge_atTop N] with n hn
  have hGapF : ∀ u ∈ F, j u ≤ -(1 / ((n : ℝ) + 1)) := by
    intro u hu
    have hm := (hMem u).1 hu
    exact hN n hn u hm.1 hm.2.1 hm.2.2
  have hL := avram_a22_original_largejump_raw_source_equals_physical_finite_mark_sum
    X ω t F hMem
  have hS := avram_a22_original_restored_compensator_smalljump_equals_physical_finite_mark_sum
    X ω t n F hMem
  calc
    _ = avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω +
      (avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω +
       (t : ℝ) * (∫ z in Ioc (-1 : ℝ)
         (-(1 / ((n : ℝ) + 1))), z ∂X.ν)) := by ring
    _ = (∑ u ∈ F, if j u ≤ -1 then j u else 0) +
      (∑ u ∈ F, if -1 < j u ∧
        j u ≤ -(1 / ((n : ℝ) + 1)) then j u else 0) := by
          rw [hL, hS]
    _ = ∑ u ∈ F, j u :=
      avram_a22_local_signed_band_partition F j n hGapF
    _ = _ := hSigned
