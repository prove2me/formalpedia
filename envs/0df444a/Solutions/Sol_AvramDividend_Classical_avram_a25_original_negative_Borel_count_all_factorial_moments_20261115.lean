-- Prove2me | solution 1 for AvramDividend.Classical.avram_a25_original_negative_Borel_count_all_factorial_moments_20261115
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:21:16.052214+00:00
-- url     : https://prove2.me/submissions/63a401f5-8cc6-4dea-a454-d35991725676

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a25_original_negative_Borel_factorial_count_compensator_recurrence_20261115
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ))
    (K : Ω → ℕ) (hK : Measurable K)
    (hCount : ∀ᵐ ω ∂P, (K ω : ℝ) =
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)).toReal)
    (r : ℝ≥0)
    (hr : (r : ℝ) = ((T : ℝ≥0∞) * X.ν B).toReal) :
    ∀ n : ℕ, (∫ ω, (Nat.descFactorial (K ω) n : ℝ) ∂P) = (r : ℝ) ^ n := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hRec :=
    avram_a25_original_negative_Borel_factorial_count_compensator_recurrence_20261115
      X hFinite T B hB hNeg K hK hCount r hr
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      (∫ ω, (Nat.descFactorial (K ω) (Nat.succ n) : ℝ) ∂P) =
          (r : ℝ) * (∫ ω, (Nat.descFactorial (K ω) n : ℝ) ∂P) := by
        simpa only [Nat.succ_eq_add_one] using hRec n
      _ = (r : ℝ) ^ Nat.succ n := by rw [ih, pow_succ]; ring
