-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual10_original_localised_negative_lintegral_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T17:30:16.040014+00:00
-- url     : https://prove2.me/submissions/775ddcf1-4405-4b4e-bb05-948dff97c78d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_finite_coordinate_event_exhaustion
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_finite_coordinate_event_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Original-row coefficient clipping exhausts the extended negative
expectation, even when the untruncated source is not integrable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (n : ℕ) (a : Ω → ℕ → ℝ)
    (ha : ∀ i, Measurable (fun ω => a ω i))
    (f : Ω → ℝ) (hf : Measurable f) :
    Tendsto
      (fun k : ℕ => ∫⁻ ω, ({z : Ω | ∀ i ∈ Finset.range (n + 1),
        abs (a z i) ≤ (k : ℝ)}).indicator
        (fun z => ENNReal.ofReal (-f z)) ω ∂P)
      atTop (𝓝 (∫⁻ ω, ENNReal.ofReal (-f ω) ∂P)) := by
  let A : ℕ → Set Ω := fun k =>
    {z | ∀ i ∈ Finset.range (n + 1), abs (a z i) ≤ (k : ℝ)}
  let F : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (-f ω)
  let g : ℕ → Ω → ℝ≥0∞ := fun k => (A k).indicator F
  have hA : ∀ k, MeasurableSet (A k) := fun k =>
    avram_bv_residual10_finite_coordinate_event_measurable n a ha k
  have hg : ∀ k, AEMeasurable (g k) P := by
    intro k
    exact ((hf.neg.ennreal_ofReal).indicator (hA k)).aemeasurable
  have hmono : ∀ ω, Monotone (fun k => g k ω) := by
    intro ω i j hij
    have hsub : A i ⊆ A j := by
      intro z hz t ht
      exact (hz t ht).trans (by exact_mod_cast hij)
    by_cases hi : ω ∈ A i
    · have hj : ω ∈ A j := hsub hi
      simp [g, Set.indicator, hi, hj]
    · by_cases hj : ω ∈ A j
      · simp [g, Set.indicator, hi, hj]
      · simp [g, Set.indicator, hi, hj]
  have hlim : ∀ ω, Tendsto (fun k => g k ω) atTop (𝓝 (F ω)) := by
    intro ω
    obtain ⟨N, hN⟩ :=
      avram_bv_residual10_finite_coordinate_event_exhaustion n a ω
    have hevent : ∀ᶠ k : ℕ in atTop, ω ∈ A k :=
      (eventually_ge_atTop N).mono (fun k hk => hN k hk)
    have heq : (fun k => g k ω) =ᶠ[atTop] fun _ => F ω := by
      filter_upwards [hevent] with k hk
      simp [g, Set.indicator, hk]
    exact (tendsto_congr' heq).2 tendsto_const_nhds
  exact lintegral_tendsto_of_tendsto_of_monotone hg
    (Filter.Eventually.of_forall hmono)
    (Filter.Eventually.of_forall hlim)
