-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_positive_exponential_image_high_moment_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:51:21.595959+00:00
-- url     : https://prove2.me/submissions/547c9c12-f329-4e8f-8c02-b75241de61e1

import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

theorem solution
    (μ : Measure ℝ) (R : ℝ) (hR : 1 < R) (k : ℕ) :
    ENNReal.ofReal (R ^ k) * μ (Set.Ici R) ≤
      ∫⁻ z, ENNReal.ofReal (z ^ k) ∂μ := by
  let g : ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (z ^ k)
  have hg : Measurable g := by
    dsimp [g]
    fun_prop
  have hR0 : 0 ≤ R := by linarith
  have hs : Set.Ici R ⊆ {z | ENNReal.ofReal (R ^ k) ≤ g z} := by
    intro z hz
    apply ENNReal.ofReal_le_ofReal
    gcongr
    exact hz
  change ENNReal.ofReal (R ^ k) * μ (Set.Ici R) ≤ ∫⁻ z, g z ∂μ
  calc
    ENNReal.ofReal (R ^ k) * μ (Set.Ici R) ≤
        ENNReal.ofReal (R ^ k) *
          μ {z | ENNReal.ofReal (R ^ k) ≤ g z} := by
      gcongr
    _ ≤ ∫⁻ z, g z ∂μ :=
      MeasureTheory.mul_meas_ge_le_lintegral hg (ENNReal.ofReal (R ^ k))
