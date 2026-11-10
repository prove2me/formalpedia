-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_excess24_original_full_negative_count_grid_collision_L1_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T22:05:42.428339+00:00
-- url     : https://prove2.me/submissions/293bd7be-6cc8-48e5-8c22-f42eb53552b4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_excess22_original_source_collision_lintegral_vanish
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_intrinsic_grid_count_eq_source_jump_count_ae_short_partition
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_bv_original_fullmark_all_time_intervals_exact_rate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact original-source fullmark collision mass is asymptotically negligible in L1. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T)
    (grid : ℕ → ℕ → ℝ≥0) (cells : ℕ → ℕ)
    (hStrict : ∀ n, StrictMono (grid n))
    (hZero : ∀ n, grid n 0 = 0)
    (hEnd : ∀ n, grid n (cells n) = T)
    (hMesh : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in (Filter.atTop : Filter ℕ),
        ∀ i : ℕ, i < cells n →
          dist (grid n i) (grid n (i + 1)) < δ)
    (hDiffMeas : ∀ n, Measurable (fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ (Set.univ : Set ℝ)) -
      ({i : ℕ | i < cells n ∧ ∃ u : ℝ≥0,
      u ≤ T ∧ 0 < u ∧
      X.X u ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
      u ∈ Ioc (grid n i) (grid n (i + 1))}.ncard : ℝ≥0∞))) :
    Filter.Tendsto (fun n => ∫⁻ ω,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ (Set.univ : Set ℝ)) -
      ({i : ℕ | i < cells n ∧ ∃ u : ℝ≥0,
      u ≤ T ∧ 0 < u ∧
      X.X u ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
      u ∈ Ioc (grid n i) (grid n (i + 1))}.ncard : ℝ≥0∞) ∂P)
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by
  let N : Ω → ℝ≥0∞ := fun ω => ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ (Set.univ : Set ℝ))
  let K : ℕ → Ω → ℝ≥0∞ := fun n ω => ({i : ℕ | i < cells n ∧ ∃ u : ℝ≥0,
      u ≤ T ∧ 0 < u ∧
      X.X u ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
      u ∈ Ioc (grid n i) (grid n (i + 1))}.ncard : ℝ≥0∞)
  change Filter.Tendsto (fun n => ∫⁻ ω, N ω - K n ω ∂P)
    Filter.atTop (nhds (0 : ℝ≥0∞))
  apply avram_bv_excess22_original_source_collision_lintegral_vanish
    P K N ?_ ?_ ?_
  · intro n
    exact hDiffMeas n
  · change (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ (Set.univ : Set ℝ)) ∂P) < ⊤
    rw [avram_wave6_01_bv_original_fullmark_all_time_intervals_exact_rate
      X hBV hFinite 0 T (show (0 : ℝ≥0) ≤ T by exact zero_le)]
    simpa using (ENNReal.mul_lt_top (by simp : ((T : ℝ≥0∞) < ⊤)) hFinite)
  · filter_upwards [avram_wave4_04a_bv_actual_intrinsic_grid_count_eq_source_jump_count_ae_short_partition
      X hBV hFinite T hT] with ω hω
    obtain ⟨δ, hδ, hocc⟩ := hω
    filter_upwards [hMesh δ hδ] with n hn
    exact (hocc (cells n) (grid n) (hStrict n) (hZero n)
      (hEnd n) hn).symm
