-- Prove2me | solution 1 for AvramDividend.Classical.avram_a122_original_arbitrary_Borel_mark_void_natural_time_power_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:30:53.603843+00:00
-- url     : https://prove2.me/submissions/c2d43a57-71e2-4c1d-82b0-1b1aaba45620

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a121_original_arbitrary_Borel_mark_void_unconditional_semigroup_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a113_original_zero_horizon_physical_negative_Borel_count_pathwise_zero_20261114

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Repeated original-filtration void-semigroup factorisation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) (k : ℕ) :
    (let p : ℝ≥0 → ENNReal := fun s =>
      P {ω : Ω |
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 s ×ˢ B) = 0}
     p ((k : ℝ≥0) * T) = (p T) ^ k) := by
  classical
  let p : ℝ≥0 → ENNReal := fun s =>
    P {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 s ×ˢ B) = 0}
  have hsem : ∀ s t : ℝ≥0, p (s + t) = p s * p t := by
    intro s t
    simpa only [p] using
      (avram_a121_original_arbitrary_Borel_mark_void_unconditional_semigroup_20261114 X s t B hB)
  have hzero : p 0 = 1 := by
    letI : IsProbabilityMeasure P := X.isProbability
    have hVoid : ∀ ω : Ω,
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 (0 : ℝ≥0) ×ˢ B) = 0 :=
      avram_a113_original_zero_horizon_physical_negative_Borel_count_pathwise_zero_20261114 X B
    have hUniv : {ω : Ω |
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 (0 : ℝ≥0) ×ˢ B) = 0} = Set.univ := by
      ext ω
      simp [hVoid ω]
    simp [p, hUniv]
  change p ((k : ℝ≥0) * T) = (p T) ^ k
  induction k with
  | zero =>
      simpa using hzero
  | succ j ih =>
      have htime : (((j + 1 : ℕ) : ℝ≥0) * T) =
          ((j : ℝ≥0) * T) + T := by
        rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
      calc
        p (((j + 1 : ℕ) : ℝ≥0) * T) =
            p (((j : ℝ≥0) * T) + T) := by rw [htime]
        _ = p ((j : ℝ≥0) * T) * p T := hsem _ _
        _ = (p T) ^ (j + 1) := by rw [ih, pow_succ]
