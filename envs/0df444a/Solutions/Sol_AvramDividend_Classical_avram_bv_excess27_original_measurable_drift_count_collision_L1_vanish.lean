-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_excess27_original_measurable_drift_count_collision_L1_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T22:28:51.5012+00:00
-- url     : https://prove2.me/submissions/52ecf0c1-20c2-490f-9f87-a7283cab4d8b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_excess22_original_source_collision_lintegral_vanish
import Theorems.Thm_AvramDividend_Classical_avram_bv_excess26_original_grid_drift_deficit_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_intrinsic_grid_count_eq_source_jump_count_ae_short_partition
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_grid_occupied_jump_cells_iff_drift_deficits_ae
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_intrinsic_marked_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_bv_original_fullmark_all_time_intervals_exact_rate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Measurable original drift-deficit surrogate gives the full cofinal count-collision L1 limit. -/
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
          dist (grid n i) (grid n (i + 1)) < δ) :
    Filter.Tendsto (fun n => ∫⁻ ω,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ (Set.univ : Set ℝ)) -
      (∑ i ∈ Finset.range (cells n),
        if X.X (grid n (i + 1)) ω - X.X (grid n i) ω <
           X.drift * (((grid n (i + 1) - grid n i : ℝ≥0) : ℝ))
        then (1 : ℝ≥0∞) else 0) ∂P)
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by
  classical
  let N : Ω → ℝ≥0∞ := fun ω => ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ (Set.univ : Set ℝ))
  let K : ℕ → Ω → ℝ≥0∞ := fun n ω =>
      ∑ i ∈ Finset.range (cells n),
        if X.X (grid n (i + 1)) ω - X.X (grid n i) ω <
           X.drift * (((grid n (i + 1) - grid n i : ℝ≥0) : ℝ))
        then (1 : ℝ≥0∞) else 0
  change Filter.Tendsto (fun n => ∫⁻ ω, N ω - K n ω ∂P)
    Filter.atTop (nhds (0 : ℝ≥0∞))
  apply avram_bv_excess22_original_source_collision_lintegral_vanish
    P K N ?_ ?_ ?_
  · intro n
    have hmN : Measurable N := by
      exact avram_p2_e_compensator_original_intrinsic_marked_count_measurable
        X 0 T (show (0 : ℝ≥0) ≤ T by exact zero_le)
        Set.univ MeasurableSet.univ
    have hmK : Measurable (K n) := by
      exact avram_bv_excess26_original_grid_drift_deficit_count_measurable
        X (grid n) (cells n)
    exact hmN.sub hmK
  · change (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ (Set.univ : Set ℝ)) ∂P) < ⊤
    rw [avram_wave6_01_bv_original_fullmark_all_time_intervals_exact_rate
      X hBV hFinite 0 T (show (0 : ℝ≥0) ≤ T by exact zero_le)]
    simpa using (ENNReal.mul_lt_top (by simp : ((T : ℝ≥0∞) < ⊤)) hFinite)
  · filter_upwards [
      avram_wave4_04a_bv_actual_intrinsic_grid_count_eq_source_jump_count_ae_short_partition
        X hBV hFinite T hT,
      avram_wave4_04a_bv_actual_grid_occupied_jump_cells_iff_drift_deficits_ae
        X hBV hFinite T hT] with ω hSmall hDef
    obtain ⟨δ, hδ, hSmallδ⟩ := hSmall
    filter_upwards [hMesh δ hδ] with n hWidth
    have hBound : ∀ i : ℕ, i < cells n →
        grid n i ≤ grid n (i + 1) ∧ grid n (i + 1) ≤ T := by
      intro i hi
      constructor
      · exact (hStrict n).monotone (Nat.le_succ i)
      · rw [← hEnd n]
        exact (hStrict n).monotone (by omega)
    have hDefEq := hDef (cells n) (grid n) hBound
    have hRawEq : {i : ℕ | i < cells n ∧ ∃ u : ℝ≥0,
        u ≤ T ∧ 0 < u ∧
        X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
        u ∈ Ioc (grid n i) (grid n (i + 1))} =
      {i : ℕ | i < cells n ∧ ∃ u : ℝ≥0,
        u ∈ Ioc (grid n i) (grid n (i + 1)) ∧
        X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u ≠ 0} := by
      ext i
      constructor
      · rintro ⟨hi, u, huT, hu0, hjump, hcell⟩
        exact ⟨hi, u, hcell, hjump⟩
      · rintro ⟨hi, u, hcell, hjump⟩
        have huT : u ≤ T := le_trans hcell.2 (hBound i hi).2
        have hu0 : 0 < u :=
          lt_of_le_of_lt
            (show (0 : ℝ≥0) ≤ grid n i by exact zero_le) hcell.1
        exact ⟨hi, u, huT, hu0, hjump, hcell⟩
    have hEq : N ω =
        ({i : ℕ | i < cells n ∧
          X.X (grid n (i + 1)) ω - X.X (grid n i) ω <
            X.drift * (((grid n (i + 1) - grid n i : ℝ≥0) : ℝ))}.ncard :
          ℝ≥0∞) := by
      have hh := hSmallδ (cells n) (grid n) (hStrict n)
        (hZero n) (hEnd n) hWidth
      rw [hRawEq, hDefEq] at hh
      exact hh
    rw [hEq]
    have hSet : {i : ℕ | i < cells n ∧
        X.X (grid n (i + 1)) ω - X.X (grid n i) ω <
          X.drift * (((grid n (i + 1) - grid n i : ℝ≥0) : ℝ))} =
      ↑((Finset.range (cells n)).filter (fun i =>
        X.X (grid n (i + 1)) ω - X.X (grid n i) ω <
          X.drift * (((grid n (i + 1) - grid n i : ℝ≥0) : ℝ)))) := by
      ext i
      simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter,
        Finset.mem_range]
    rw [hSet, Set.ncard_coe_finset]
    dsimp [K]
    simp [Finset.sum_ite, Finset.sum_const]
