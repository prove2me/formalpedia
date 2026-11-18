-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_bounded_marked_count_pgf_monotone_unit_interval_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T17:28:23.657477+00:00
-- url     : https://prove2.me/submissions/8c02c140-8bb1-462c-a89d-35ed00f60403

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a27_bounded_marked_count_pgf_integrable_20261117
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A nonnegative marked-count probability generating function is monotone on the unit interval. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (F : Ω → ℝ) (hF : Measurable F)
    (hRange : ∀ᵐ ω ∂P, 0 ≤ F ω ∧ F ω ≤ 1)
    (z w : ℝ) (hz : 0 ≤ z) (hzw : z ≤ w) (hw : w ≤ 1) :
    (∫ ω, z ^ (K ω) * F ω ∂P) ≤
      (∫ ω, w ^ (K ω) * F ω ∂P) := by
  have hw0 : 0 ≤ w := le_trans hz hzw
  have hPower : ∀ n : ℕ, z ^ n ≤ w ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n hn =>
      rw [pow_succ, pow_succ]
      calc
        z ^ n * z ≤ w ^ n * z :=
          mul_le_mul_of_nonneg_right hn hz
        _ ≤ w ^ n * w :=
          mul_le_mul_of_nonneg_left hzw (pow_nonneg hw0 _)
  have hIz :=
    avram_a27_bounded_marked_count_pgf_integrable_20261117
      P K hK F hF hRange z hz (le_trans hzw hw)
  have hIw :=
    avram_a27_bounded_marked_count_pgf_integrable_20261117
      P K hK F hF hRange w hw0 hw
  apply integral_mono_ae hIz hIw
  filter_upwards [hRange] with ω hω
  exact mul_le_mul_of_nonneg_right (hPower (K ω)) hω.1
