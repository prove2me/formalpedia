-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_01_original_future_grid_deficit_weighted_first_moment_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T23:41:28.436016+00:00
-- url     : https://prove2.me/submissions/2fb28984-b051-4a58-bc50-10f39b0e61fc

import Mathlib.Probability.Independence.Integration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_source_future_grid_deficit_count_indep_past
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (H : Ω → ℝ≥0∞)
    (hH : Measurable[𝓕 s] H)
    (n : ℕ) (grid : ℕ → ℝ≥0) :
    (∫⁻ ω, H ω * (((Finset.range n).filter (fun i =>
      (X.X (s + grid (i + 1)) ω - X.X s ω) -
        (X.X (s + grid i) ω - X.X s ω) <
        X.drift * (((grid (i + 1) - grid i : ℝ≥0) : ℝ)))).card : ℝ≥0∞) ∂P) =
      (∫⁻ ω, H ω ∂P) *
      (∫⁻ ω, (((Finset.range n).filter (fun i =>
        (X.X (s + grid (i + 1)) ω - X.X s ω) -
          (X.X (s + grid i) ω - X.X s ω) <
          X.drift * (((grid (i + 1) - grid i : ℝ≥0) : ℝ)))).card : ℝ≥0∞) ∂P) := by
  classical
  let p : ℕ → Ω → Prop := fun i ω =>
    (X.X (s + grid (i + 1)) ω - X.X s ω) -
      (X.X (s + grid i) ω - X.X s ω) <
      X.drift * (((grid (i + 1) - grid i : ℝ≥0) : ℝ))
  let D : Ω → ℕ := fun ω =>
    ((Finset.range n).filter (fun i => p i ω)).card
  have hp (i : ℕ) : MeasurableSet {ω : Ω | p i ω} := by
    have hleft : Measurable (fun ω : Ω => X.X (s + grid i) ω) :=
      (X.adapted (s + grid i)).mono (𝓕.le (s + grid i)) le_rfl
    have hright : Measurable (fun ω : Ω => X.X (s + grid (i + 1)) ω) :=
      (X.adapted (s + grid (i + 1))).mono
        (𝓕.le (s + grid (i + 1))) le_rfl
    have hbase : Measurable (fun ω : Ω => X.X s ω) :=
      (X.adapted s).mono (𝓕.le s) le_rfl
    exact measurableSet_lt ((hright.sub hbase).sub (hleft.sub hbase))
      measurable_const
  have hSum : Measurable (fun ω : Ω =>
      ∑ i ∈ Finset.range n, if p i ω then (1 : ℕ) else 0) := by
    apply Finset.measurable_sum
    intro i hi
    exact Measurable.ite (hp i) measurable_const measurable_const
  have hEq :
      (fun ω : Ω => ((Finset.range n).filter (fun i => p i ω)).card) =
      (fun ω : Ω => ∑ i ∈ Finset.range n, if p i ω then (1 : ℕ) else 0) := by
    funext ω
    exact Finset.card_filter (fun i => p i ω) (Finset.range n)
  have hD : Measurable D := by
    change Measurable (fun ω : Ω =>
      ((Finset.range n).filter (fun i => p i ω)).card)
    rw [hEq]
    exact hSum
  have hCast : Measurable (fun k : ℕ => (k : ℝ≥0∞)) :=
    measurable_of_countable _
  have hDCast : Measurable (fun ω : Ω => (D ω : ℝ≥0∞)) :=
    hCast.comp hD
  have hHglobal : Measurable H := hH.mono (𝓕.le s) le_rfl
  have hIndepRaw : IndepFun H D P :=
    avram_wave4_04a_actual_source_future_grid_deficit_count_indep_past
      X s H hH n grid
  have hIndep : IndepFun H (fun ω : Ω => (D ω : ℝ≥0∞)) P := by
    have hc := hIndepRaw.comp measurable_id hCast
    simpa only [Function.comp_def, id_eq] using hc
  change (∫⁻ ω, H ω * (D ω : ℝ≥0∞) ∂P) =
    (∫⁻ ω, H ω ∂P) * (∫⁻ ω, (D ω : ℝ≥0∞) ∂P)
  exact lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
    hHglobal hDCast hIndep
