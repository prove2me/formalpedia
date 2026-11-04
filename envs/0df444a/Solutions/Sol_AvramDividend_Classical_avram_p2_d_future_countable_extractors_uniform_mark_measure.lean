-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_d_future_countable_extractors_uniform_mark_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:01:27.193193+00:00
-- url     : https://prove2.me/submissions/9b7cd327-6086-46fb-b84a-185ef4c59930

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_countable_mark_extractors_past_factor
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_uniform_past_mark_mean_measure_product

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The measurable original future-path extraction family for a countable
Borel mark class has one shared original mean mark measure for every coordinate
and every event measurable in the original past. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : ℕ → Set ℝ) (hB : ∀ n, MeasurableSet (B n)) :
    ∃ (ρ : Measure ℝ) (F : ℕ → ((ℝ≥0 → ℝ) → ℝ≥0∞)),
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
          X.X (s + v) ω - X.X s ω) ∂P) = P A * ρ (B n)) := by
  obtain ⟨ρ, hρ⟩ :=
    avram_p2_d_future_uniform_past_mark_mean_measure_product X s t hst
  obtain ⟨F, hFmeas, hExact, _hFactor⟩ :=
    avram_p2_d_future_countable_mark_extractors_past_factor
      X s t hst B hB
  refine ⟨ρ, F, hFmeas, hExact, ?_⟩
  intro n A hA
  calc
    (∫⁻ ω in A, F n (fun v : ℝ≥0 =>
      X.X (s + v) ω - X.X s ω) ∂P) =
      (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B n) ∂P) := by
          apply lintegral_congr
          intro ω
          exact (hExact n ω).symm
    _ = P A * ρ (B n) := hρ A hA (B n) (hB n)
