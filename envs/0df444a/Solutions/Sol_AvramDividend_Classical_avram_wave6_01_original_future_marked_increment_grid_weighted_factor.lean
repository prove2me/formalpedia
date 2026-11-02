-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_01_original_future_marked_increment_grid_weighted_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T23:49:50.11374+00:00
-- url     : https://prove2.me/submissions/bb40aa56-5f7e-489e-9bcb-9121fda59718

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_actual_levy_past_indep_measurable_future_jump_family_ws01b
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (H : Ω → ℝ≥0∞)
    (hH : Measurable[𝓕 s] H)
    (B : Set ℝ) (hB : MeasurableSet B)
    (n : ℕ) (grid : ℕ → ℝ≥0) :
    (∫⁻ ω, H ω * (((Finset.range n).filter (fun i =>
      (X.X (s + grid (i + 1)) ω - X.X s ω) -
        (X.X (s + grid i) ω - X.X s ω) ∈ B)).card : ℝ≥0∞) ∂P) =
      (∫⁻ ω, H ω ∂P) *
      (∫⁻ ω, (((Finset.range n).filter (fun i =>
        (X.X (s + grid (i + 1)) ω - X.X s ω) -
          (X.X (s + grid i) ω - X.X s ω) ∈ B)).card : ℝ≥0∞) ∂P) := by
  classical
  let p : ℕ → (ℝ≥0 → ℝ) → Prop := fun i Y =>
    Y (grid (i + 1)) - Y (grid i) ∈ B
  have hp (i : ℕ) : MeasurableSet {Y : ℝ≥0 → ℝ | p i Y} := by
    exact hB.preimage
      ((measurable_pi_apply (grid (i + 1))).sub (measurable_pi_apply (grid i)))
  have hSum : Measurable (fun Y : ℝ≥0 → ℝ =>
      ∑ i ∈ Finset.range n, if p i Y then (1 : ℕ) else 0) := by
    apply Finset.measurable_sum
    intro i hi
    exact Measurable.ite (hp i) measurable_const measurable_const
  have hEq :
      (fun Y : ℝ≥0 → ℝ =>
        ((Finset.range n).filter (fun i => p i Y)).card) =
      (fun Y : ℝ≥0 → ℝ =>
        ∑ i ∈ Finset.range n, if p i Y then (1 : ℕ) else 0) := by
    funext Y
    exact Finset.card_filter (fun i => p i Y) (Finset.range n)
  let Fpath : (ℝ≥0 → ℝ) → ℕ := fun Y =>
    ((Finset.range n).filter (fun i => p i Y)).card
  have hF : Measurable Fpath := by
    change Measurable (fun Y : ℝ≥0 → ℝ =>
      ((Finset.range n).filter (fun i => p i Y)).card)
    rw [hEq]
    exact hSum
  have hCast : Measurable (fun k : ℕ => (k : ℝ≥0∞)) :=
    measurable_of_countable _
  have hFuture : Measurable
      (fun ω : Ω => fun t : ℝ≥0 => X.X (s + t) ω - X.X s ω) := by
    have hXm : ∀ t, Measurable (X.X t) := fun t =>
      (X.adapted t).mono (𝓕.le t) le_rfl
    exact measurable_pi_lambda _ (fun t => (hXm _).sub (hXm _))
  have hDCast : Measurable (fun ω : Ω =>
      (Fpath (fun t : ℝ≥0 => X.X (s + t) ω - X.X s ω) : ℝ≥0∞)) :=
    hCast.comp (hF.comp hFuture)
  have hHglobal : Measurable H := hH.mono (𝓕.le s) le_rfl
  have hIndepRaw : IndepFun H
      (fun ω : Ω => Fpath (fun t : ℝ≥0 => X.X (s + t) ω - X.X s ω)) P :=
    actual_levy_past_indep_measurable_future_jump_family_ws01b
      X s H hH Fpath hF
  have hIndep : IndepFun H (fun ω : Ω =>
      (Fpath (fun t : ℝ≥0 => X.X (s + t) ω - X.X s ω) : ℝ≥0∞)) P := by
    have hc := hIndepRaw.comp measurable_id hCast
    simpa only [Function.comp_def, id_eq] using hc
  change (∫⁻ ω, H ω *
    (Fpath (fun t : ℝ≥0 => X.X (s + t) ω - X.X s ω) : ℝ≥0∞) ∂P) =
    (∫⁻ ω, H ω ∂P) *
    (∫⁻ ω, (Fpath (fun t : ℝ≥0 => X.X (s + t) ω - X.X s ω) : ℝ≥0∞) ∂P)
  exact lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
    hHglobal hDCast hIndep
