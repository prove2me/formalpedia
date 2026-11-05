-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_f_chainlimit_original_unmarked_finite_marks_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T15:06:45.358553+00:00
-- url     : https://prove2.me/submissions/b2e94e70-c0c9-41c9-bd39-8721c5fb5b8a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_finite_source_tagged_capture
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_uniform_ae_unmarked_J_finite_exclusion
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (u : ℕ → ℝ≥0) (n : ℕ) (T : Finset ℝ≥0)
    (hCover : ∀ v ∈ T, ∃ i : ℕ,
      i < n ∧ u i < v ∧ v ≤ u (i + 1))
    (hSeparate : ∀ v ∈ T, ∀ z ∈ T, ∀ i : ℕ,
      i < n → u i < v → v ≤ u (i + 1) →
      u i < z → z ≤ u (i + 1) → v = z) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' s : ℝ≥0, if 0 < s ∧ s ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) s - X.X s ω
        else 0
      ∃ tag : ℝ≥0 → ℕ,
        (∀ v ∈ T,
          tag v < n ∧ u (tag v) < v ∧ v ≤ u (tag v + 1)) ∧
        (∀ v ∈ T, ∀ z ∈ T, tag v = tag z → v = z) ∧
        (Finset.range n).sum (fun i =>
          if i ∈ T.image tag then 0
          else J (u (i + 1)) - J (u i)) ≤
        J (u n) - J (u 0) -
          T.sum (fun v =>
            Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω) := by
  filter_upwards
    [avram_p3_f_chainlimit_original_finite_source_tagged_capture
      X hBV u n T hCover hSeparate,
      avram_p3_f_chainlimit_original_uniform_ae_unmarked_J_finite_exclusion
        X hBV] with ω htag htail
  intro J
  obtain ⟨tag, hcell, hinj, _⟩ := htag
  have hTag : ∀ v ∈ T, tag v < n :=
    fun v hv => (hcell v hv).1
  have hInside : ∀ v ∈ T,
      u (tag v) < v ∧ v ≤ u (tag v + 1) :=
    fun v hv => (hcell v hv).2
  refine ⟨tag, hcell, hinj, ?_⟩
  exact htail u n T tag hTag hinj hInside
