-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_jump8_turn11_original_shortcell_integrability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T12:55:03.869259+00:00
-- url     : https://prove2.me/submissions/a02f4738-387b-42ae-a5cd-c25810613fd7

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn11_original_shortcell_product_pointwise_bounds
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cutoff_marked_count_L1_auto
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn12_original_weighted_observables_aestronglyMeasurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn12_original_loss_closed_count_domination

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- A.e. measurability plus domination by the genuine integrable original
closed count establish Bochner integrability of both marked observables. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (k n : ℕ) :
    let T : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
    let S : Ω → Finset ℝ≥0 := fun ω =>
      (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset
    let W : Ω → ℝ := fun ω => ∏ u ∈ S ω,
      Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
    let L : Ω → ℝ := fun ω => ∑ u ∈ S ω,
      (1 - Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
    Integrable W P ∧ Integrable L P := by
  letI : IsProbabilityMeasure P := X.isProbability
  let T : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
  let S : Ω → Finset ℝ≥0 := fun ω =>
    (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset
  let W : Ω → ℝ := fun ω => ∏ u ∈ S ω,
    Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
  let L : Ω → ℝ := fun ω => ∑ u ∈ S ω,
    (1 - Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iic (-(1 / ((k : ℝ) + 1))))
  have hm : AEStronglyMeasurable W P ∧ AEStronglyMeasurable L P := by
    simpa only [T, S, W, L] using
      (avram_bv_jump8_turn12_original_weighted_observables_aestronglyMeasurable
        X hX hBV k n)
  have hdom : ∀ ω : Ω, 0 ≤ L ω ∧ L ω ≤ (N ω).toReal := by
    simpa only [T, S, L, N] using
      (avram_bv_jump8_turn12_original_loss_closed_count_domination
        X hX hBV k n)
  have hN : Integrable (fun ω => (N ω).toReal) P := by
    simpa only [T, N] using
      (avram_p4_f_assembly_original_cutoff_marked_count_L1_auto X T k)
  have hWrange : ∀ ω : Ω, 0 ≤ W ω ∧ W ω ≤ 1 := by
    simpa only [T, S, W] using
      (avram_bv_jump8_turn11_original_shortcell_product_pointwise_bounds
        X hX hBV k n)
  have hWbound : ∀ᵐ ω ∂P, ‖W ω‖ ≤ (1 : ℝ) :=
    Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hWrange ω).1]
      exact (hWrange ω).2)
  have hLbound : ∀ᵐ ω ∂P, ‖L ω‖ ≤ (N ω).toReal :=
    Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hdom ω).1]
      exact (hdom ω).2)
  change Integrable W P ∧ Integrable L P
  exact ⟨(integrable_const (1 : ℝ)).mono' hm.1 hWbound,
    hN.mono' hm.2 hLbound⟩
