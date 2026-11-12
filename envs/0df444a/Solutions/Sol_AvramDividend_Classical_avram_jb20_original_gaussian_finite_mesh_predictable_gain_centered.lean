-- Prove2me | solution 1 for AvramDividend.Classical.avram_jb20_original_gaussian_finite_mesh_predictable_gain_centered
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T17:15:47.900522+00:00
-- url     : https://prove2.me/submissions/e62a24d0-e658-49b1-93db-04331d8b9ca7

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_jb20_original_gaussian_past_weight_increment_mean_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The entire finite original right-continuous predictable Gaussian mesh
is L1 and centred once each physical martingale cell is integrable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {ι : Type*} (S : Finset ι)
    (R : ℝ≥0 → Ω → ℝ)
    (hRint : ∀ u : ℝ≥0, Integrable (R u) P)
    (hRmart : ∀ u v : ℝ≥0, u ≤ v →
      ∀ᵐ ω ∂P,
        condExp (𝓕.rightCont u) P (R v) ω = R u ω)
    (a b : ι → ℝ≥0) (W : ι → Ω → ℝ)
    (hab : ∀ i ∈ S, a i ≤ b i)
    (hW : ∀ i ∈ S,
      Measurable[𝓕.rightCont (a i)] (W i))
    (K : ℝ)
    (hWbound : ∀ i ∈ S, ∀ ω, ‖W i ω‖ ≤ K) :
    Integrable
      (fun ω => ∑ i ∈ S,
        W i ω * (R (b i) ω - R (a i) ω)) P ∧
    (∫ ω, ∑ i ∈ S,
      W i ω * (R (b i) ω - R (a i) ω) ∂P) = 0 := by
  classical
  have hProd (i : ι) (hi : i ∈ S) :
      Integrable
        (fun ω => W i ω * (R (b i) ω - R (a i) ω)) P := by
    have hDiff : Integrable
        (fun ω => R (b i) ω - R (a i) ω) P := by
      exact (hRint (b i)).sub (hRint (a i))
    have hWm : Measurable (W i) :=
      (hW i hi).mono ((𝓕.rightCont).le (a i)) le_rfl
    exact hDiff.bdd_mul hWm.aestronglyMeasurable
      (Filter.Eventually.of_forall (hWbound i hi))
  have hEach (i : ι) (hi : i ∈ S) :
      (∫ ω, W i ω * (R (b i) ω - R (a i) ω) ∂P) = 0 :=
    avram_jb20_original_gaussian_past_weight_increment_mean_zero
      R hRint hRmart (a i) (b i) (hab i hi)
      (W i) (hW i hi) (hProd i hi)
  refine ⟨integrable_finset_sum S hProd, ?_⟩
  rw [integral_finset_sum S hProd]
  exact Finset.sum_eq_zero hEach
