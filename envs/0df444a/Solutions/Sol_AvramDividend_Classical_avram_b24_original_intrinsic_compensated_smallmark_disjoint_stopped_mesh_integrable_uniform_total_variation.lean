-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_original_intrinsic_compensated_smallmark_disjoint_stopped_mesh_integrable_uniform_total_variation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:51:53.508188+00:00
-- url     : https://prove2.me/submissions/e0a236c5-3e2f-4793-9198-16a7ac524ce0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_finiteactivity_smallmark_increment_true_interval_count_variation_ae
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_smallnegative_physical_mark_count_exact_finite_support_card
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_arbitrary_intrinsic_smallmark_uniform_horizon_L1_envelope
import Theorems.Thm_AvramDividend_Classical_avram_b24_actual_finite_marked_times_disjoint_physical_cells_count_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X :
    SpectrallyNegativeLevy P 𝓕) (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) (Jsmall : ℝ≥0 → Ω → ℝ) (hJsource :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, Tendsto (fun n : ℕ => avram_p4_h_gaussian_intrinsic_small_band_compensated X
    n t ω) atTop (𝓝 (Jsmall t ω))) (T : ℝ≥0) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Ioo (-1 : ℝ) 0)
    let B : Ω → ℝ := fun ω => (N ω).toReal +
      (T : ℝ) * ‖∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν‖
    Integrable B P ∧ ∀ᵐ ω ∂P, ∀ (I : Finset ℕ) (a b : ℕ → ℝ≥0), (∀ i ∈ I, a i ≤ b i ∧ b i ≤ T) → (∀
    i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (Ioc (a i) (b i)) (Ioc (a j) (b j))) → (∑ i ∈ I, ((b i : ℝ) -
    (a i : ℝ))) ≤ (T : ℝ) → (∑ i ∈ I, ‖Jsmall (b i) ω - Jsmall (a i) ω‖) ≤ B ω := by
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Ioo (-1 : ℝ) 0)
  let d : ℝ := ∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν
  let B : Ω → ℝ := fun ω => (N ω).toReal + (T : ℝ) * ‖d‖
  change Integrable B P ∧
    ∀ᵐ ω ∂P, ∀ (I : Finset ℕ) (a b : ℕ → ℝ≥0),
      (∀ i ∈ I, a i ≤ b i ∧ b i ≤ T) →
      (∀ i ∈ I, ∀ j ∈ I, i ≠ j →
        Disjoint (Ioc (a i) (b i)) (Ioc (a j) (b j))) →
      (∑ i ∈ I, ((b i : ℝ) - (a i : ℝ))) ≤ (T : ℝ) →
      (∑ i ∈ I, ‖Jsmall (b i) ω - Jsmall (a i) ω‖) ≤ B ω
  have hEnv :=
    AvramDividend.Classical.avram_b24_original_arbitrary_intrinsic_smallmark_uniform_horizon_L1_envelope
      X hFinite Jsmall hJsource T
  change Integrable B P ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T → ‖Jsmall t ω‖ ≤ B ω)
    at hEnv
  have hPath :=
    AvramDividend.Classical.avram_b24_original_finiteactivity_smallmark_increment_true_interval_count_variation_ae
      X hFinite Jsmall hJsource T
  refine ⟨hEnv.1, ?_⟩
  filter_upwards [hPath] with ω hω
  obtain ⟨S, hS, hVariation⟩ := hω
  let z : ℝ≥0 → ℝ := fun u =>
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
  let Sm := S.filter (fun u => -1 < z u ∧ z u < 0)
  have hSm (u : ℝ≥0) :
      u ∈ Sm ↔ 0 < u ∧ u ≤ T ∧ z u ∈ Ioo (-1 : ℝ) 0 := by
    simp only [Sm, Finset.mem_filter]
    constructor
    · intro hu
      have hs := (hS u).1 hu.1
      exact ⟨hs.1, hs.2.1, hu.2⟩
    · intro hu
      have hne : z u ≠ 0 := ne_of_lt hu.2.2.2
      exact ⟨(hS u).2 ⟨hu.1, hu.2.1, hne⟩, hu.2.2⟩
  have hN : (N ω).toReal = (Sm.card : ℝ) := by
    have heq := AvramDividend.Classical.avram_b24_original_smallnegative_physical_mark_count_exact_finite_support_card
      X ω T Sm (by simpa only [z] using hSm)
    change N ω = (Sm.card : ℝ≥0∞) at heq
    rw [heq]
    simp
  intro I a b hCell hDisj hLen
  have hCountNat :
      (∑ i ∈ I, (Sm.filter (fun u => a i < u ∧ u ≤ b i)).card) ≤ Sm.card :=
    AvramDividend.Classical.avram_b24_actual_finite_marked_times_disjoint_physical_cells_count_budget
      Sm I a b (fun i hi => (hCell i hi).1) hDisj
  have hCount :
      (∑ i ∈ I, ((Sm.filter (fun u => a i < u ∧ u ≤ b i)).card : ℝ)) ≤
        (Sm.card : ℝ) := by exact_mod_cast hCountNat
  have hEach (i : ℕ) (hi : i ∈ I) :
      ‖Jsmall (b i) ω - Jsmall (a i) ω‖ ≤
        ((Sm.filter (fun u => a i < u ∧ u ≤ b i)).card : ℝ) +
        ((b i : ℝ) - (a i : ℝ)) * ‖d‖ := by
    have hv := hVariation (a i) (b i) (hCell i hi).1 (hCell i hi).2
    simpa [Sm, z, d, Finset.filter_filter, and_assoc, and_left_comm, and_comm]
      using hv
  have hSum := Finset.sum_le_sum (fun i hi => hEach i hi)
  have hDrift : (∑ i ∈ I, ((b i : ℝ) - (a i : ℝ))) * ‖d‖ ≤
      (T : ℝ) * ‖d‖ :=
    mul_le_mul_of_nonneg_right hLen (norm_nonneg d)
  change (∑ i ∈ I, ‖Jsmall (b i) ω - Jsmall (a i) ω‖) ≤
      (N ω).toReal + (T : ℝ) * ‖d‖
  rw [hN]
  calc
    (∑ i ∈ I, ‖Jsmall (b i) ω - Jsmall (a i) ω‖) ≤
      (∑ i ∈ I, (((Sm.filter (fun u => a i < u ∧ u ≤ b i)).card : ℝ) +
        ((b i : ℝ) - (a i : ℝ)) * ‖d‖)) := hSum
    _ = (∑ i ∈ I, ((Sm.filter (fun u => a i < u ∧ u ≤ b i)).card : ℝ)) +
        (∑ i ∈ I, ((b i : ℝ) - (a i : ℝ))) * ‖d‖ := by
      rw [Finset.sum_add_distrib, Finset.sum_mul]
    _ ≤ (Sm.card : ℝ) + (T : ℝ) * ‖d‖ :=
      add_le_add hCount hDrift
