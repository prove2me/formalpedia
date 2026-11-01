-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_bv_actual_intrinsic_grid_count_eq_source_jump_count_ae_short_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T22:21:23.029399+00:00
-- url     : https://prove2.me/submissions/3b0b8ebd-aade-4303-a101-3a12271c2665

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_source_jump_times_finite_on_horizon
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_separated_jumps_one_per_short_cell_ae
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_count_eq_finite_grid_occupancy_of_unique_cover
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

private theorem strict_grid_covers_positive_interval
    (T : ℝ≥0) (n : ℕ) (grid : ℕ → ℝ≥0)
    (hZero : grid 0 = 0) (hEnd : grid n = T)
    (u : ℝ≥0) (hu0 : 0 < u) (huT : u ≤ T) :
    ∃ i : ℕ, i < n ∧ u ∈ Ioc (grid i) (grid (i + 1)) := by
  classical
  let hEx : ∃ k : ℕ, u ≤ grid k := ⟨n, by simpa [hEnd] using huT⟩
  let k : ℕ := Nat.find hEx
  have hk : u ≤ grid k := Nat.find_spec hEx
  have hkle : k ≤ n := Nat.find_le (by simpa [hEnd] using huT)
  have hkpos : 0 < k := by
    by_contra hnot
    have hzero : k = 0 := by omega
    have hz : u ≤ (0 : ℝ≥0) := by simpa [hzero, hZero] using hk
    exact (not_le_of_gt hu0) hz
  have hbefore : ¬u ≤ grid (k - 1) :=
    Nat.find_min hEx (by omega)
  have hleft : grid (k - 1) < u := lt_of_not_ge hbefore
  have hright : u ≤ grid ((k - 1) + 1) := by
    simpa [Nat.sub_add_cancel (show 1 ≤ k from hkpos)] using hk
  exact ⟨k - 1, by omega, hleft, hright⟩

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P, ∃ δ : ℝ, 0 < δ ∧
      ∀ (n : ℕ) (grid : ℕ → ℝ≥0),
        StrictMono grid → grid 0 = 0 → grid n = T →
        (∀ i : ℕ, i < n →
          dist (grid i) (grid (i + 1)) < δ) →
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω - Function.leftLim
            (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ (Set.univ : Set ℝ)) =
        ({i : ℕ | i < n ∧ ∃ u : ℝ≥0,
          u ≤ T ∧ 0 < u ∧
          X.X u ω - Function.leftLim
            (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
          u ∈ Ioc (grid i) (grid (i + 1))}.ncard : ENNReal) := by
  have hFiniteSource :=
    avram_wave4_04a_bv_actual_source_jump_times_finite_on_horizon
      X hBV hFinite T hT
  have hOneSource :=
    avram_wave4_04a_bv_actual_separated_jumps_one_per_short_cell_ae
      X hBV hFinite T hT
  filter_upwards [hFiniteSource, hOneSource] with ω hFiniteω hOneω
  obtain ⟨δ, hδ, hOne⟩ := hOneω
  refine ⟨δ, hδ, ?_⟩
  intro n grid hStrict hZero hEnd hWidth
  let S : Set ℝ≥0 :=
    {u : ℝ≥0 | u ≤ T ∧ 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}
  have hSfinite : S.Finite := hFiniteω
  have hS :
      S = {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0} := by
    ext u
    simp only [S, Set.mem_setOf_eq]
    tauto
  have hCover : ∀ u : ℝ≥0, u ∈ S →
      ∃ i : ℕ, i < n ∧ u ∈ Ioc (grid i) (grid (i + 1)) := by
    intro u hu
    exact strict_grid_covers_positive_interval T n grid hZero hEnd
      u hu.2.1 hu.1
  have hSingle : ∀ i : ℕ, i < n → ∀ u v : ℝ≥0,
      u ∈ S → v ∈ S →
      u ∈ Ioc (grid i) (grid (i + 1)) →
      v ∈ Ioc (grid i) (grid (i + 1)) → u = v := by
    intro i hi u v hu hv huc hvc
    exact hOne n grid hWidth i hi u v hu hv huc hvc
  have hIndexUnique : ∀ u : ℝ≥0, u ∈ S → ∀ i j : ℕ,
      i < n → j < n →
      u ∈ Ioc (grid i) (grid (i + 1)) →
      u ∈ Ioc (grid j) (grid (j + 1)) → i = j := by
    intro u hu i j hi hj huc hjc
    by_contra hne
    rcases lt_or_gt_of_ne hne with hij | hji
    · have hle : grid (i + 1) ≤ grid j :=
        hStrict.monotone (by omega)
      exact (not_lt_of_ge (le_trans huc.2 hle)) hjc.1
    · have hle : grid (j + 1) ≤ grid i :=
        hStrict.monotone (by omega)
      exact (not_lt_of_ge (le_trans hjc.2 hle)) huc.1
  have hCore :=
    avram_wave4_04a_actual_intrinsic_jump_count_eq_finite_grid_occupancy_of_unique_cover
      X ω T n grid S hS hSfinite hCover hSingle hIndexUnique
  simpa only [S, Set.mem_setOf_eq, and_assoc] using hCore
