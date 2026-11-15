-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_original_intrinsic_smallmark_true_stopped_chronological_grid_uniform_L1_variation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:53:43.6262+00:00
-- url     : https://prove2.me/submissions/7a1e0921-0b9e-4572-bfa0-9603762a02cf

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_intrinsic_smallmark_chronological_refining_physical_grid_uniform_integrable_variation
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
      ∀ᵐ ω ∂P, ∀ (n : ℕ) (t : ℕ → ℝ≥0)
        (σ : Ω → ℝ≥0), Monotone t → t n ≤ T →
        (∑ i ∈ Finset.range n,
          ‖Jsmall (min (t (i + 1)) (σ ω)) ω -
            Jsmall (min (t i) (σ ω)) ω‖) ≤ B ω := by
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
    ∀ᵐ ω ∂P, ∀ (n : ℕ) (t : ℕ → ℝ≥0)
      (σ : Ω → ℝ≥0), Monotone t → t n ≤ T →
      (∑ i ∈ Finset.range n,
        ‖Jsmall (min (t (i + 1)) (σ ω)) ω -
          Jsmall (min (t i) (σ ω)) ω‖) ≤ B ω
  have hUnif :=
    AvramDividend.Classical.avram_b24_original_intrinsic_smallmark_chronological_refining_physical_grid_uniform_integrable_variation
      X hFinite Jsmall hJsource T
  change Integrable B P ∧
    (∀ᵐ ω ∂P, ∀ (n : ℕ) (t : ℕ → ℝ≥0),
      Monotone t → t n ≤ T →
      (∑ i ∈ Finset.range n,
        ‖Jsmall (t (i + 1)) ω - Jsmall (t i) ω‖) ≤ B ω)
    at hUnif
  refine ⟨hUnif.1, ?_⟩
  filter_upwards [hUnif.2] with ω hω
  intro n t σ hmono ht
  let s : ℕ → ℝ≥0 := fun i => min (t i) (σ ω)
  have hmonoS : Monotone s := by
    intro i j hij
    dsimp [s]
    exact min_le_min (hmono hij) le_rfl
  have hsT : s n ≤ T :=
    (min_le_left _ _).trans ht
  exact hω n s hmonoS hsT
