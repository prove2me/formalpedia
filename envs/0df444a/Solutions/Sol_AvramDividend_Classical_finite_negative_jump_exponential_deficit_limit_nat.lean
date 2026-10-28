-- Prove2me | solution 1 for AvramDividend.Classical.finite_negative_jump_exponential_deficit_limit_nat
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:37:52.500806+00:00
-- url     : https://prove2.me/submissions/13a08709-a581-438e-b0c4-a8fa99a1c324

import Theorems.Thm_AvramDividend_Classical_finite_negative_jump_exp_integral_tendsto_zero_nat
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Analysis.SpecialFunctions.Exp
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology

/-- The finite-activity Laplace exponent deficit tends to the full jump mass. -/
theorem solution
    (ν : Measure ℝ) (hFinite : ν (Iio (0 : ℝ)) < ⊤) :
    Tendsto (fun n : ℕ =>
      ∫ y in Iio (0 : ℝ), (1 - Real.exp ((n : ℝ) * y)) ∂ν)
      atTop (𝓝 (ν (Iio (0 : ℝ))).toReal) := by
  let μ : Measure ℝ := ν.restrict (Iio (0 : ℝ))
  letI : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    simpa [μ] using hFinite
  have hmem : ∀ᵐ y : ℝ ∂μ, y < 0 :=
    ae_restrict_mem measurableSet_Iio
  have hInt (n : ℕ) :
      Integrable (fun y : ℝ => Real.exp ((n : ℝ) * y)) μ := by
    apply Integrable.mono' (integrable_const (1 : ℝ))
    · exact ((Real.continuous_exp.comp
        (continuous_const.mul continuous_id)).measurable).aestronglyMeasurable
    · filter_upwards [hmem] with y hy
      have hy0 : (n : ℝ) * y ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (le_of_lt hy)
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact (Real.exp_le_one_iff).2 hy0
  have hSplit (n : ℕ) :
      (∫ y in Iio (0 : ℝ), (1 - Real.exp ((n : ℝ) * y)) ∂ν) =
        (ν (Iio (0 : ℝ))).toReal -
          (∫ y in Iio (0 : ℝ), Real.exp ((n : ℝ) * y) ∂ν) := by
    change (∫ y : ℝ, (1 - Real.exp ((n : ℝ) * y)) ∂μ) =
      (ν (Iio (0 : ℝ))).toReal -
        (∫ y : ℝ, Real.exp ((n : ℝ) * y) ∂μ)
    rw [integral_sub (integrable_const _) (hInt n)]
    simp [μ, Measure.real_def]
  have hDecay :=
    AvramDividend.Classical.finite_negative_jump_exp_integral_tendsto_zero_nat ν hFinite
  have hFinal :=
    (tendsto_const_nhds.sub hDecay :
      Tendsto (fun n : ℕ =>
        (ν (Iio (0 : ℝ))).toReal -
          (∫ y in Iio (0 : ℝ), Real.exp ((n : ℝ) * y) ∂ν))
        atTop (𝓝 ((ν (Iio (0 : ℝ))).toReal - 0)))
  simpa only [hSplit, sub_zero] using hFinal
