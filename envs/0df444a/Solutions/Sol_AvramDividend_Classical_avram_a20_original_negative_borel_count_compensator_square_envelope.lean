-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_original_negative_borel_count_compensator_square_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T21:04:46.679868+00:00
-- url     : https://prove2.me/submissions/16a57bb5-ffc0-4c80-a6fa-9ef00aecac2b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_negative_borel_real_count_square_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ja35_original_negative_borel_real_count_first_moment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ)) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    Integrable (fun ω => ((N ω).toReal + r) ^ 2) P := by
  letI : IsProbabilityMeasure P := X.isProbability
  intro N r
  have hN2 : Integrable (fun ω => ((N ω).toReal) ^ 2) P := by
    simpa only [N] using
      (avram_a20_original_negative_borel_real_count_square_integrable
        X hFinite T B hB hNeg)
  have hN1 : Integrable (fun ω => (N ω).toReal) P := by
    simpa only [N] using
      (avram_ja35_original_negative_borel_real_count_first_moment
        X hFinite T B hB hNeg).1
  have hEq : (fun ω => ((N ω).toReal + r) ^ 2) =
      (fun ω => ((N ω).toReal) ^ 2 +
        (2 * r) * (N ω).toReal + r ^ 2) := by
    funext ω
    ring
  rw [hEq]
  exact (hN2.add (hN1.const_mul (2 * r))).add
    (integrable_const (r ^ 2))
