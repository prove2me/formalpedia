-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_bounded_marked_count_pgf_integrable_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T17:11:22.532708+00:00
-- url     : https://prove2.me/submissions/1fa92f6e-9d09-4083-94a8-dedcba0aa297

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A bounded mark factor gives an integrable count-weighted PGF on any probability space. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (F : Ω → ℝ) (hF : Measurable F)
    (hRange : ∀ᵐ ω ∂P, 0 ≤ F ω ∧ F ω ≤ 1)
    (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    Integrable (fun ω => z ^ (K ω) * F ω) P := by
  have hPow : ∀ n : ℕ, z ^ n ≤ (1 : ℝ) := by
    intro n
    induction n with
    | zero => simp
    | succ n hn =>
      rw [pow_succ]
      calc
        z ^ n * z ≤ (1 : ℝ) * z :=
          mul_le_mul_of_nonneg_right hn hz
        _ = z := one_mul z
        _ ≤ 1 := hz1
  have hMeas : Measurable (fun ω => z ^ (K ω) * F ω) :=
    (measurable_const.pow hK).mul hF
  apply (integrable_const (1 : ℝ)).mono hMeas.aestronglyMeasurable
  filter_upwards [hRange] with ω hω
  have hp0 : 0 ≤ z ^ K ω := pow_nonneg hz _
  have hp1 : z ^ K ω ≤ 1 := hPow (K ω)
  have hprod0 : 0 ≤ z ^ K ω * F ω := mul_nonneg hp0 hω.1
  have hprod1 : z ^ K ω * F ω ≤ 1 := by
    calc
      z ^ K ω * F ω ≤ (1 : ℝ) * F ω :=
        mul_le_mul_of_nonneg_right hp1 hω.1
      _ = F ω := one_mul _
      _ ≤ 1 := hω.2
  calc
    ‖z ^ K ω * F ω‖ = z ^ K ω * F ω := by
      rw [Real.norm_eq_abs, abs_of_nonneg hprod0]
    _ ≤ 1 := hprod1
    _ = ‖(1 : ℝ)‖ := by norm_num
