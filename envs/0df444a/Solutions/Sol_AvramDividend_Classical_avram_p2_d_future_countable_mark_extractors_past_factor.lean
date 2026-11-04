-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_d_future_countable_mark_extractors_past_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:25:52.423193+00:00
-- url     : https://prove2.me/submissions/6b17345c-8c1a-4b53-a46f-b8289da151cc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_extractor_past_event_factor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- A countable family of original future-path marked-count extractors is
jointly measurable in the product and factors against the original past. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : ℕ → Set ℝ) (hB : ∀ n, MeasurableSet (B n)) :
    ∃ F : ℕ → ((ℝ≥0 → ℝ) → ℝ≥0∞),
      Measurable (fun y : ℝ≥0 → ℝ => fun n : ℕ => F n y) ∧
      (∀ (n : ℕ) (ω : Ω),
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ B n) =
          F n (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω)) ∧
      (∀ (n : ℕ) (A : Set Ω), MeasurableSet[𝓕 s] A →
        (∫⁻ ω in A, F n (fun v : ℝ≥0 =>
          X.X (s + v) ω - X.X s ω) ∂P) =
        P A * (∫⁻ ω, F n (fun v : ℝ≥0 =>
          X.X (s + v) ω - X.X s ω) ∂P)) := by
  classical
  have hEach (n : ℕ) :=
    avram_p2_d_future_extractor_past_event_factor X s t hst (B n) (hB n)
  choose F hFmeas hExact hPast using hEach
  refine ⟨F, ?_, hExact, hPast⟩
  apply measurable_pi_iff.mpr
  exact hFmeas
