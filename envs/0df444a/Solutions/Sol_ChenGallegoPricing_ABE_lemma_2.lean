-- Prove2me | solution 1 for ChenGallegoPricing.ABE.lemma_2
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-29T06:04:19.835622+00:00
-- url     : https://prove2.me/submissions/666fa999-6c36-44ff-bdcd-faae56176076

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace S226N_169dac73

noncomputable def f (b : Bool) : ℝ := if b then 1 else 0

lemma hf : Measurable f := measurable_of_finite f

noncomputable def μ : Measure Bool := (1/2 : ℝ≥0∞) • Measure.dirac true + (1/2 : ℝ≥0∞) • Measure.dirac false

instance : IsProbabilityMeasure μ := ⟨by simp [μ, ENNReal.inv_two_add_inv_two]⟩

noncomputable def κ : Kernel Bool ℝ := Kernel.deterministic f hf

instance : IsMarkovKernel κ := by unfold κ; infer_instance

lemma comp_eq : κ ∘ₘ ProbabilityTheory.cond μ Set.univ =
    (1/2 : ℝ≥0∞) • Measure.dirac (1:ℝ) + (1/2 : ℝ≥0∞) • Measure.dirac (0:ℝ) := by
  rw [ProbabilityTheory.cond_univ, κ, Measure.deterministic_comp_eq_map, μ,
    Measure.map_add _ _ hf, Measure.map_smul, Measure.map_smul]
  simp [Measure.map_dirac' hf, f]

end S226N_169dac73

open S226N_169dac73 in
theorem solution : ¬ (∀ {X : Type} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (B : Set X)
    (hB : MeasurableSet B) (hpos : μ B ≠ 0)
    (κ : Kernel X ℝ) [IsMarkovKernel κ] (σ : ℝ≥0)
    (hcomponents : ∀ x ∈ B, Integrable id (κ x) ∧
      HasSubgaussianMGF (fun z => z - ∫ y, y ∂κ x) (2 * σ) (κ x))
    (hmean : Integrable id (κ ∘ₘ ProbabilityTheory.cond μ B)),
    HasSubgaussianMGF
      (fun z => z - ∫ y, y ∂(κ ∘ₘ ProbabilityTheory.cond μ B))
      (2 * σ) (κ ∘ₘ ProbabilityTheory.cond μ B)) := by
  intro H
  have hcomp : ∀ x, ∀ hx : x ∈ (Set.univ : Set Bool), Integrable id (κ x) ∧
      HasSubgaussianMGF (fun z => z - ∫ y, y ∂κ x) (2 * (0:ℝ≥0)) (κ x) := by
    intro x _
    simp only [κ, Kernel.deterministic_apply, integral_dirac, mul_zero]
    refine ⟨integrable_dirac (by simp), ?_⟩
    refine (HasSubgaussianMGF.zero (μ := Measure.dirac (f x))).congr ?_
    rw [Filter.EventuallyEq, ae_dirac_eq, Filter.eventually_pure]
    simp
  have hmean : Integrable id (κ ∘ₘ ProbabilityTheory.cond μ Set.univ) := by
    rw [comp_eq]
    refine Integrable.add_measure ?_ ?_ <;>
      exact (integrable_dirac (by simp)).smul_measure (by simp)
  have h := H μ Set.univ MeasurableSet.univ (by rw [measure_univ]; exact one_ne_zero) κ 0 hcomp hmean
  rw [mul_zero] at h
  have h0 := h.ae_eq_zero_of_hasSubgaussianMGF_zero
  rw [comp_eq] at h0
  set m := ∫ y, y ∂((1/2 : ℝ≥0∞) • Measure.dirac (1:ℝ) + (1/2 : ℝ≥0∞) • Measure.dirac (0:ℝ))
  rw [Filter.EventuallyEq, ae_add_measure_iff] at h0
  obtain ⟨h1, h2⟩ := h0
  rw [ae_iff, Measure.smul_apply, Measure.dirac_apply] at h1 h2
  simp [Set.indicator] at h1 h2
  linarith
