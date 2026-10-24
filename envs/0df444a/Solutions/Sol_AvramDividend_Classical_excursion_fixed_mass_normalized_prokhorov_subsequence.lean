-- Prove2me | solution 1 for AvramDividend.Classical.excursion_fixed_mass_normalized_prokhorov_subsequence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T23:17:38.982344+00:00
-- url     : https://prove2.me/submissions/ef0a7870-0024-4c92-a965-c1f97ffeb220

import Mathlib.MeasureTheory.Measure.Prokhorov
import Theorems.Thm_AvramDividend_Classical_excursion_fixed_mass_normalization_preserves_tightness
import Theorems.Thm_AvramDividend_Classical_excursion_prokhorov_probability_tight_subsequence

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set

/-!
Combining uniform tightness under positive fixed-mass
normalisation with Prokhorov compactness yields a convergent
probability-normalised subsequence of finite measures.
-/
theorem solution
    (ν : ℕ → FiniteMeasure ℝ) (c : NNReal) (hc : 0 < c)
    (hmass : ∀ n : ℕ, (ν n).mass = c)
    (hnz : ∀ n : ℕ, ν n ≠ 0)
    (htight : IsTightMeasureSet
      (Set.range (fun n : ℕ => (ν n : Measure ℝ)))) :
    ∃ (P : ProbabilityMeasure ℝ) (φ : ℕ → ℕ),
      StrictMono φ ∧
      Tendsto (fun n : ℕ => (ν (φ n)).normalize) atTop (𝓝 P) := by
  have hn :=
    AvramDividend.Classical.excursion_fixed_mass_normalization_preserves_tightness
      ν c hc hmass hnz htight
  have heq :
      {x : Measure ℝ |
        ∃ p ∈ Set.range (fun n : ℕ => (ν n).normalize),
          (p : Measure ℝ) = x} =
      Set.range (fun n : ℕ => ((ν n).normalize : Measure ℝ)) := by
    ext μ
    constructor
    · rintro ⟨p, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨(ν n).normalize, ⟨n, rfl⟩, rfl⟩
  have htightP : IsTightMeasureSet
      {x : Measure ℝ |
        ∃ p ∈ Set.range (fun n : ℕ => (ν n).normalize),
          (p : Measure ℝ) = x} := by
    rw [heq]
    exact hn
  obtain ⟨P, φ, hφ, hlim⟩ :=
    AvramDividend.Classical.excursion_prokhorov_probability_tight_subsequence
      (fun n => (ν n).normalize) htightP
  exact ⟨P, φ, hφ, hlim⟩
