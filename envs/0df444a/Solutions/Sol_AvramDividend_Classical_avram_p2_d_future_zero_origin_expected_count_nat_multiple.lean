-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_d_future_zero_origin_expected_count_nat_multiple
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:26:50.049137+00:00
-- url     : https://prove2.me/submissions/859e1216-556d-4381-a09f-8272fc4f7167

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_zero_origin_expected_count_additive

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- At every positive or zero physical horizon, the original count mean
over n copies of that horizon is n times its mean, including infinite counts. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (B : Set ℝ) (hB : MeasurableSet B)
    (t : ℝ≥0) (n : ℕ) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 ((n : ℝ≥0) * t) ×ˢ B) ∂P) =
      (n : ℝ≥0∞) * (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 t ×ˢ B) ∂P) := by
  let M : ℝ≥0 → ℝ≥0∞ := fun q =>
    ∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 q ×ˢ B) ∂P
  have hAdd (a b : ℝ≥0) : M (a + b) = M a + M b := by
    simpa only [M] using
      (avram_p2_d_future_zero_origin_expected_count_additive X a b B hB)
  change M ((n : ℝ≥0) * t) = (n : ℝ≥0∞) * M t
  induction n with
  | zero =>
      simp [M]
  | succ n ih =>
      calc
        M (((Nat.succ n : ℕ) : ℝ≥0) * t) =
            M ((n : ℝ≥0) * t + t) := by
              congr 1
              simp [Nat.cast_succ, add_mul]
        _ = M ((n : ℝ≥0) * t) + M t :=
          hAdd ((n : ℝ≥0) * t) t
        _ = (n : ℝ≥0∞) * M t + M t := by rw [ih]
        _ = ((Nat.succ n : ℕ) : ℝ≥0∞) * M t := by
              rw [Nat.cast_succ, add_mul]
              simp