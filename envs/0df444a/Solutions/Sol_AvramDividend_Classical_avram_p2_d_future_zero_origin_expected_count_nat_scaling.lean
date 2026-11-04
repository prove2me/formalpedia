-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_d_future_zero_origin_expected_count_nat_scaling
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:26:44.662198+00:00
-- url     : https://prove2.me/submissions/6afa7725-0bc9-4d41-afc6-91de4f040197

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_zero_origin_expected_count_additive

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Original expected literal marked counts scale exactly at integer physical
times with their unit-time mean, even if that mean is infinite. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (B : Set ℝ) (hB : MeasurableSet B) (n : ℕ) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (n : ℝ≥0) ×ˢ B) ∂P) =
      (n : ℝ≥0∞) *
        (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 (1 : ℝ≥0) ×ˢ B) ∂P) := by
  let M : ℝ≥0 → ℝ≥0∞ := fun t =>
    ∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 t ×ˢ B) ∂P
  have hAdd (a b : ℝ≥0) : M (a + b) = M a + M b := by
    simpa only [M] using
      (avram_p2_d_future_zero_origin_expected_count_additive X a b B hB)
  change M (n : ℝ≥0) = (n : ℝ≥0∞) * M 1
  induction n with
  | zero =>
      simp [M]
  | succ n ih =>
      calc
        M ((Nat.succ n : ℕ) : ℝ≥0) =
            M (n : ℝ≥0) + M 1 := by
              simpa only [Nat.cast_succ] using
                (hAdd (n : ℝ≥0) 1)
        _ = (n : ℝ≥0∞) * M 1 + M 1 := by rw [ih]
        _ = ((Nat.succ n : ℕ) : ℝ≥0∞) * M 1 := by
              rw [Nat.cast_succ, add_mul]
              simp