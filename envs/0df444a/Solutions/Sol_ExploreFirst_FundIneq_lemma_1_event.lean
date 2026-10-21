-- Prove2me | solution 1 for ExploreFirst.FundIneq.lemma_1_event
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:50:06.247658+00:00
-- url     : https://prove2.me/submissions/bca4ffad-2393-4a17-91fa-1044721780d4

import Mathlib
import Definitions.Def_ExploreFirst_FundIneq_Setting

set_option autoImplicit false
open MeasureTheory ProbabilityTheory InformationTheory unitInterval
open ExploreFirst.FundIneq
open scoped ENNReal

lemma efi_product {Γ : Type*} [MeasurableSpace Γ] (P₁ P₂ : Measure Γ)
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] :
    klDiv P₁ P₂ =
      klDiv (P₁.prod (volume : Measure unitInterval)) (P₂.prod (volume : Measure unitInterval)) := by
  apply le_antisymm
  · have h := klDiv_map_le (μ := P₁.prod (volume : Measure unitInterval))
      (ν := P₂.prod (volume : Measure unitInterval)) (g := Prod.fst) measurable_fst
    simpa using h
  · rw [← Measure.compProd_const, ← Measure.compProd_const]
    exact (klDiv_compProd_left (μ := P₁) (ν := P₂)
      (κ := Kernel.const Γ (volume : Measure unitInterval))).le

lemma efi_map_indicator {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (E : Set α) (hE : MeasurableSet E) :
    μ.map (E.indicator (fun _ => (1 : ℝ))) = bernoulliLaw (μ.real E) := by
  ext s hs
  rw [Measure.map_apply (measurable_const.indicator hE) hs]
  unfold bernoulliLaw
  have h1 : ENNReal.ofReal (μ.real E) = μ E := ofReal_measureReal (measure_ne_top _ _)
  have h2 : ENNReal.ofReal (1 - μ.real E) = μ Eᶜ := by
    rw [← probReal_compl_eq_one_sub hE]
    exact ofReal_measureReal (measure_ne_top _ _)
  simp only [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ hs, smul_eq_mul, h1, h2]
  by_cases h1s : (1 : ℝ) ∈ s <;> by_cases h0s : (0 : ℝ) ∈ s
  · have : E.indicator (fun _ => (1 : ℝ)) ⁻¹' s = Set.univ := by
      ext x; by_cases hx : x ∈ E <;> simp [Set.indicator, hx, h1s, h0s]
    rw [this]
    simp [Set.indicator, h1s, h0s, measure_add_measure_compl hE]
  · have : E.indicator (fun _ => (1 : ℝ)) ⁻¹' s = E := by
      ext x; by_cases hx : x ∈ E <;> simp [Set.indicator, hx, h1s, h0s]
    rw [this]
    simp [Set.indicator, h1s, h0s]
  · have : E.indicator (fun _ => (1 : ℝ)) ⁻¹' s = Eᶜ := by
      ext x; by_cases hx : x ∈ E <;> simp [Set.indicator, hx, h1s, h0s]
    rw [this]
    simp [Set.indicator, h1s, h0s]
  · have : E.indicator (fun _ => (1 : ℝ)) ⁻¹' s = ∅ := by
      ext x; by_cases hx : x ∈ E <;> simp [Set.indicator, hx, h1s, h0s]
    rw [this]
    simp [Set.indicator, h1s, h0s]

theorem solution {Γ : Type*} [MeasurableSpace Γ] (P₁ P₂ : Measure Γ)
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    (E : Set (Γ × unitInterval)) (hE : MeasurableSet E) :
    klBer ((P₁.prod (volume : Measure unitInterval)).real E)
        ((P₂.prod (volume : Measure unitInterval)).real E) ≤ klDiv P₁ P₂ := by
  rw [efi_product P₁ P₂]
  unfold klBer
  rw [← efi_map_indicator (P₁.prod (volume : Measure unitInterval)) E hE,
    ← efi_map_indicator (P₂.prod (volume : Measure unitInterval)) E hE]
  exact klDiv_map_le _ _ (measurable_const.indicator hE)
