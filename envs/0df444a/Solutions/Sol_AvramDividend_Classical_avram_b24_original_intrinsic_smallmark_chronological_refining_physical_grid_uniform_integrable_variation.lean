-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_original_intrinsic_smallmark_chronological_refining_physical_grid_uniform_integrable_variation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:53:35.403184+00:00
-- url     : https://prove2.me/submissions/d09ace57-ce11-4a06-931a-555f6cdd1b42

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_intrinsic_compensated_smallmark_disjoint_stopped_mesh_integrable_uniform_total_variation
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_physical_chronological_finite_grid_total_duration_telescope
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_monotone_chronological_physical_mesh_cells_pairwise_disjoint_Ioc
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
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω)
        atTop (𝓝 (Jsmall t ω)))
    (T : ℝ≥0) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Ioo (-1 : ℝ) 0)
    let B : Ω → ℝ := fun ω => (N ω).toReal +
      (T : ℝ) * ‖∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν‖
    Integrable B P ∧
      ∀ᵐ ω ∂P, ∀ (n : ℕ) (t : ℕ → ℝ≥0),
        Monotone t → t n ≤ T →
        (∑ i ∈ Finset.range n,
          ‖Jsmall (t (i + 1)) ω - Jsmall (t i) ω‖) ≤ B ω := by
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Ioo (-1 : ℝ) 0)
  let B : Ω → ℝ := fun ω => (N ω).toReal +
    (T : ℝ) * ‖∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν‖
  change Integrable B P ∧
    ∀ᵐ ω ∂P, ∀ (n : ℕ) (t : ℕ → ℝ≥0),
      Monotone t → t n ≤ T →
      (∑ i ∈ Finset.range n,
        ‖Jsmall (t (i + 1)) ω - Jsmall (t i) ω‖) ≤ B ω
  have hUniform :=
    AvramDividend.Classical.avram_b24_original_intrinsic_compensated_smallmark_disjoint_stopped_mesh_integrable_uniform_total_variation
      X hFinite Jsmall hJsource T
  change Integrable B P ∧
    (∀ᵐ ω ∂P, ∀ (I : Finset ℕ) (a b : ℕ → ℝ≥0),
      (∀ i ∈ I, a i ≤ b i ∧ b i ≤ T) →
      (∀ i ∈ I, ∀ j ∈ I, i ≠ j →
        Disjoint (Ioc (a i) (b i)) (Ioc (a j) (b j))) →
      (∑ i ∈ I, ((b i : ℝ) - (a i : ℝ))) ≤ (T : ℝ) →
      (∑ i ∈ I, ‖Jsmall (b i) ω - Jsmall (a i) ω‖) ≤ B ω)
    at hUniform
  refine ⟨hUniform.1, ?_⟩
  filter_upwards [hUniform.2] with ω hω
  intro n t hmono hT
  have hCell : ∀ i ∈ Finset.range n,
      t i ≤ t (i + 1) ∧ t (i + 1) ≤ T := by
    intro i hi
    have hi' : i + 1 ≤ n :=
      Nat.succ_le_of_lt (Finset.mem_range.mp hi)
    exact ⟨hmono (Nat.le_succ i), (hmono hi').trans hT⟩
  have hDisj :=
    AvramDividend.Classical.avram_b24_original_monotone_chronological_physical_mesh_cells_pairwise_disjoint_Ioc
      t hmono (Finset.range n)
  have hDuration :=
    (AvramDividend.Classical.avram_b24_original_physical_chronological_finite_grid_total_duration_telescope
      t n T hT).2
  exact hω (Finset.range n) t (fun i => t (i + 1))
    hCell hDisj hDuration
