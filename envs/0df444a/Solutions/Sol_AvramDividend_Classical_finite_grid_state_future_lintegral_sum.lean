-- Prove2me | solution 1 for AvramDividend.Classical.finite_grid_state_future_lintegral_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T12:26:01.875008+00:00
-- url     : https://prove2.me/submissions/e400d377-f74e-426c-ba04-a55e8dc04fb4

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Process.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_finite_time_state_future_product_of_cylinders

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {E : Type*} [MeasurableSpace E]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ι → ℝ≥0) (H : ι → Ω → E)
    (hH : ∀ i, Measurable[𝓕 (s i)] (H i))
    (hFinite : ∀ i, ∀ I : Finset ℝ≥0,
      Indep (⨆ t ∈ I,
        MeasurableSpace.comap
          (fun ω => X.X (s i + t) ω - X.X (s i) ω) inferInstance)
        (𝓕 (s i)) P)
    (f : ι → E × (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    (∑ i, ∫⁻ ω, f i (H i ω,
        (fun t : ℝ≥0 => X.X (s i + t) ω - X.X (s i) ω)) ∂P) =
      ∑ i, ∫⁻ h, ∫⁻ y, f i (h, y)
        ∂(Measure.map
          (fun ω => fun t : ℝ≥0 => X.X (s i + t) ω - X.X (s i) ω) P)
        ∂(Measure.map (H i) P) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  refine Finset.sum_congr rfl ?_
  intro i hi
  let Y : Ω → (ℝ≥0 → ℝ) :=
    fun ω t => X.X (s i + t) ω - X.X (s i) ω
  have hHm : Measurable (H i) := (hH i).mono (𝓕.le (s i)) le_rfl
  have hYm : Measurable Y := by
    apply measurable_pi_iff.mpr
    intro t
    have ht : Measurable (X.X (s i + t)) :=
      (X.adapted (s i + t)).mono (𝓕.le (s i + t)) le_rfl
    exact ht.sub ((X.adapted (s i)).mono (𝓕.le (s i)) le_rfl)
  have hJoint :=
    AvramDividend.Classical.finite_time_state_future_product_of_cylinders
      X (s i) (H i) (hH i) (hFinite i)
  calc
    (∫⁻ ω, f i (H i ω, Y ω) ∂P) =
        ∫⁻ z, f i z ∂(Measure.map (fun ω => (H i ω, Y ω)) P) := by
          symm
          exact MeasureTheory.lintegral_map (hf i) (hHm.prodMk hYm)
    _ = ∫⁻ z, f i z ∂((Measure.map (H i) P).prod (Measure.map Y P)) := by
          rw [hJoint]
    _ = ∫⁻ h, ∫⁻ y, f i (h, y) ∂(Measure.map Y P) ∂(Measure.map (H i) P) :=
          MeasureTheory.lintegral_prod (f i) ((hf i).aemeasurable)
