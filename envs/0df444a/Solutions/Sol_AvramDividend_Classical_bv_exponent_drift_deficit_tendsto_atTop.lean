-- Prove2me | solution 1 for AvramDividend.Classical.bv_exponent_drift_deficit_tendsto_atTop
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:48:09.410375+00:00
-- url     : https://prove2.me/submissions/e6d78ee7-da40-4156-bc0f-5f4c38caaa4e

import Theorems.Thm_AvramDividend_Classical_bv_exponent_negative_jump_deficit_exact
import Theorems.Thm_AvramDividend_Classical_negative_levy_restricted_real_deficit_tendsto_atTop
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.MeasureTheory.Measure.Restrict

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

/-- Infinite BV jump activity makes the drift-minus-exponent deficit diverge. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (hBV : X.BoundedVariation)
    (hνinf : X.ν (Iio (0 : ℝ)) = ⊤) :
    Tendsto (fun n : ℕ => X.drift * (n : ℝ) - X.ψ (n : ℝ))
      atTop atTop := by 
  have hν1 : X.ν (Iic (-1 : ℝ)) ≠ ⊤ := by
    have hle : ENNReal.ofReal 1 * X.ν (Iic (-1 : ℝ)) ≤ ∫⁻ y, ENNReal.ofReal (min 1 (y ^ 2)) ∂X.ν := by
      rw [← setLIntegral_const]
      refine le_trans (setLIntegral_mono' measurableSet_Iic ?_) (setLIntegral_le_lintegral _ _)
      intro y hy
      simp only [mem_Iic] at hy
      apply ENNReal.ofReal_le_ofReal
      apply le_min le_rfl
      nlinarith
    rw [ENNReal.ofReal_one, one_mul] at hle
    exact (lt_of_le_of_lt hle X.ν_integrable).ne
  have hIoo : IntegrableOn (fun y : ℝ => |y|) (Ioo (-1 : ℝ) 0) X.ν := by
    rw [IntegrableOn, ← lintegral_ofReal_ne_top_iff_integrable continuous_abs.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => abs_nonneg y)]
    exact hBV.2.ne
  have hInt : ∀ n : ℕ, Integrable (fun y : ℝ => 1 - Real.exp ((n : ℝ) * y))
      (X.ν.restrict (Iio (0 : ℝ))) := by
    intro n
    set g : ℝ → ℝ := fun y => (Ioo (-1 : ℝ) 0).indicator (fun y => (n : ℝ) * |y|) y +
      (Iic (-1 : ℝ)).indicator (fun _ => (1 : ℝ)) y with hg
    have hgi : Integrable g (X.ν.restrict (Iio (0 : ℝ))) := by
      apply Integrable.add
      · rw [integrable_indicator_iff measurableSet_Ioo]
        show Integrable _ ((X.ν.restrict (Iio 0)).restrict (Ioo (-1) 0))
        refine (hIoo.const_mul (n : ℝ)).mono_measure ?_
        rw [Measure.restrict_restrict measurableSet_Ioo]
        exact Measure.restrict_mono inter_subset_left le_rfl
      · rw [integrable_indicator_iff measurableSet_Iic]
        refine integrableOn_const (μ := X.ν.restrict (Iio 0)) ?_
        rw [Measure.restrict_apply measurableSet_Iic]
        exact (lt_of_le_of_lt (measure_mono inter_subset_left) hν1.lt_top).ne
    refine Integrable.mono' hgi ?_ ?_
    · exact (continuous_const.sub (Real.continuous_exp.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
    · rw [ae_restrict_iff' measurableSet_Iio]
      refine Filter.Eventually.of_forall fun y hy => ?_
      simp only [mem_Iio] at hy
      have hx : (n : ℝ) * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hy.le
      have h1 : Real.exp ((n : ℝ) * y) ≤ 1 := Real.exp_le_one_iff.mpr hx
      have h2 : 1 - Real.exp ((n : ℝ) * y) ≤ -((n : ℝ) * y) := by
        linarith [Real.add_one_le_exp ((n : ℝ) * y)]
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith), hg]
      simp only
      by_cases hy1 : y ≤ -1
      · rw [indicator_of_notMem (by simp only [mem_Ioo, not_and, not_lt]; intro h; linarith),
          indicator_of_mem (by simpa using hy1)]
        have := Real.exp_pos ((n : ℝ) * y)
        linarith
      · push_neg at hy1
        rw [indicator_of_mem (by exact ⟨hy1, hy⟩), indicator_of_notMem (by simpa using hy1),
          abs_of_neg hy]
        linarith
  have hR := negative_levy_restricted_real_deficit_tendsto_atTop X.ν hνinf hInt
  refine hR.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  exact (bv_exponent_negative_jump_deficit_exact X hBV (n : ℝ) (by exact_mod_cast hn)).symm
