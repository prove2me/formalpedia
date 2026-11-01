-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_bv_actual_intrinsic_count_level_ae_eq_measurable_liminf_grid_deficit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T22:48:27.017588+00:00
-- url     : https://prove2.me/submissions/562453af-a153-4d80-ad8e-ba37a4545439

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_jump_count_eq_drift_deficit_count_for_all_fine_partitions_ae
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_original_grid_drift_deficit_count_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T)
    (grid : ℕ → ℕ → ℝ≥0)
    (hGrid : ∀ n : ℕ, 0 < n →
      StrictMono (grid n) ∧ grid n 0 = 0 ∧ grid n n = T)
    (hMesh : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n : ℕ in atTop, ∀ i : ℕ, i < n →
        dist (grid n i) (grid n (i + 1)) < δ)
    (k : ℕ) :
    MeasurableSet (Filter.liminf
      (fun n : ℕ => {ω : Ω |
        ((Finset.range n).filter (fun i =>
          X.X (grid n (i + 1)) ω - X.X (grid n i) ω <
            X.drift * (((grid n (i + 1) - grid n i : ℝ≥0) : ℝ)))).card = k})
      atTop) ∧
      (∀ᵐ ω ∂P,
        (((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω - Function.leftLim
            (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ (Set.univ : Set ℝ))) = (k : ENNReal) ↔
          ω ∈ (Filter.liminf
      (fun n : ℕ => {ω : Ω |
        ((Finset.range n).filter (fun i =>
          X.X (grid n (i + 1)) ω - X.X (grid n i) ω <
            X.drift * (((grid n (i + 1) - grid n i : ℝ≥0) : ℝ)))).card = k})
      atTop)) := by
  classical
  let A : ℕ → Set Ω := fun n =>
    {ω : Ω |
      ((Finset.range n).filter (fun i =>
        X.X (grid n (i + 1)) ω - X.X (grid n i) ω <
          X.drift * (((grid n (i + 1) - grid n i : ℝ≥0) : ℝ)))).card = k}
  have hA (n : ℕ) : MeasurableSet (A n) := by
    exact (avram_wave4_04a_actual_original_grid_drift_deficit_count_measurable
      X n (grid n)) (measurableSet_singleton k)
  change MeasurableSet (Filter.liminf A atTop) ∧
    (∀ᵐ ω ∂P,
      (((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω - Function.leftLim
            (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ (Set.univ : Set ℝ))) = (k : ENNReal) ↔
        ω ∈ Filter.liminf A atTop)
  constructor
  · exact MeasurableSet.measurableSet_liminf hA
  · have hSource :=
      avram_wave4_04a_bv_actual_jump_count_eq_drift_deficit_count_for_all_fine_partitions_ae
        X hBV hFinite T hT
    filter_upwards [hSource] with ω hω
    obtain ⟨δ, hδ, hFine⟩ := hω
    have hEventuallyPositive : ∀ᶠ n : ℕ in atTop, 0 < n :=
      Filter.eventually_gt_atTop 0
    have hEventuallyMesh := hMesh δ hδ
    have hEventuallyCount :
        ∀ᶠ n : ℕ in atTop,
          (((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω - Function.leftLim
            (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ (Set.univ : Set ℝ))) =
          (((Finset.range n).filter (fun i =>
            X.X (grid n (i + 1)) ω - X.X (grid n i) ω <
              X.drift * (((grid n (i + 1) - grid n i : ℝ≥0) : ℝ)))).card :
              ENNReal) := by
      filter_upwards [hEventuallyPositive, hEventuallyMesh] with n hn hwidth
      obtain ⟨hstrict, hzero, hend⟩ := hGrid n hn
      have hEq := hFine n (grid n) hstrict hzero hend hwidth
      have hSet :
          {i : ℕ | i < n ∧
            X.X (grid n (i + 1)) ω - X.X (grid n i) ω <
              X.drift * (((grid n (i + 1) - grid n i : ℝ≥0) : ℝ))} =
          (↑((Finset.range n).filter (fun i =>
            X.X (grid n (i + 1)) ω - X.X (grid n i) ω <
              X.drift * (((grid n (i + 1) - grid n i : ℝ≥0) : ℝ)))) :
            Set ℕ) := by
        ext i
        simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter,
          Finset.mem_range]
      rw [hSet] at hEq
      simpa only [Set.ncard_coe_finset] using hEq
    rw [Filter.mem_liminf_iff_eventually_mem]
    constructor
    · intro hk
      filter_upwards [hEventuallyCount] with n hCount
      change ((Finset.range n).filter (fun i =>
        X.X (grid n (i + 1)) ω - X.X (grid n i) ω <
          X.drift * (((grid n (i + 1) - grid n i : ℝ≥0) : ℝ)))).card = k
      have hCast : (((Finset.range n).filter (fun i =>
          X.X (grid n (i + 1)) ω - X.X (grid n i) ω <
            X.drift * (((grid n (i + 1) - grid n i : ℝ≥0) : ℝ)))).card :
          ENNReal) = (k : ENNReal) :=
        hCount.symm.trans hk
      exact_mod_cast hCast
    · intro hEventuallyA
      obtain ⟨n, hnEq, hnA⟩ :=
        (hEventuallyCount.and hEventuallyA).exists
      have hCard : ((Finset.range n).filter (fun i =>
          X.X (grid n (i + 1)) ω - X.X (grid n i) ω <
            X.drift * (((grid n (i + 1) - grid n i : ℝ≥0) : ℝ)))).card = k :=
        hnA
      exact hnEq.trans (by exact_mod_cast hCard)
