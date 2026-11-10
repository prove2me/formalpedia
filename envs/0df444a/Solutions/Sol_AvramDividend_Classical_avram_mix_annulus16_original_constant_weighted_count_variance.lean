-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_annulus16_original_constant_weighted_count_variance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T22:30:15.73906+00:00
-- url     : https://prove2.me/submissions/bedc0073-e70d-4f1e-a31a-5ce2b59ca6a4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_original_physical_annulus_count_variance_exact
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (n m : ℕ) (hnm : n ≤ m) (c : ℝ) :
    let B : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    Integrable (fun ω => (c * ((N ω).toReal - r)) ^ 2) P ∧
      (∫ ω, (c * ((N ω).toReal - r)) ^ 2 ∂P) = c ^ 2 * r := by
  dsimp only
  obtain ⟨hI, hVar⟩ :=
    avram_mixed_source13_original_physical_annulus_count_variance_exact
      X T n m hnm
  constructor
  · simpa only [mul_pow] using hI.const_mul (c ^ 2)
  · simpa only [mul_pow, integral_const_mul, hVar]
