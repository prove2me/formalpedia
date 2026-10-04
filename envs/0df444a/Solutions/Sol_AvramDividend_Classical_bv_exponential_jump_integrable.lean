-- Prove2me | solution 1 for AvramDividend.Classical.bv_exponential_jump_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-04T09:18:34.75447+00:00
-- url     : https://prove2.me/submissions/26f63c27-a8bd-4497-9b69-6c787f0abb27

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_finite_truncated_negative_jump_moment
import Theorems.Thm_AvramDividend_Classical_discounted_jump_compensator_bound
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : AvramDividend.Classical.SpectrallyNegativeLevy P 𝓕)
    (hbv : X.BoundedVariation)
    (θ : ℝ) (hθ : 1 ≤ θ) :
    IntegrableOn (fun y : ℝ => Real.exp (θ * y) - 1)
      (Iio (0 : ℝ)) X.ν := by
  have htrunc :
      (∫⁻ y in Iio (0 : ℝ),
        ENNReal.ofReal (min (-y) 1) ∂X.ν) < ⊤ :=
    finite_truncated_negative_jump_moment X.ν X.ν_integrable hbv.2
  have hg :
      IntegrableOn (fun y : ℝ => min (-y) 1)
        (Iio (0 : ℝ)) X.ν := by
    refine ⟨by fun_prop, ?_⟩
    change (∫⁻ y in Iio (0 : ℝ),
      ‖min (-y) (1 : ℝ)‖ₑ ∂X.ν) < ⊤
    have hae : (fun y : ℝ => ‖min (-y) (1 : ℝ)‖ₑ) =ᵐ[
        X.ν.restrict (Iio (0 : ℝ))]
        (fun y : ℝ => ENNReal.ofReal (min (-y) 1)) := by
      filter_upwards [ae_restrict_mem measurableSet_Iio] with y hy
      have hyn : y < 0 := hy
      have hneg : 0 ≤ -y := neg_nonneg.mpr hyn.le
      have hmin : 0 ≤ min (-y) (1 : ℝ) :=
        le_min hneg (by norm_num)
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hmin]
    exact (lintegral_congr_ae hae).trans_lt htrunc
  have hmajor : ∀ᵐ y ∂X.ν.restrict (Iio (0 : ℝ)),
      ‖Real.exp (θ * y) - 1‖ ≤
        ‖θ * min (-y) 1‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Iio] with y hy
    have hθpos : 0 < θ := lt_of_lt_of_le (by norm_num) hθ
    have hyn : y < 0 := hy
    have hnonneg : 0 ≤ -y := neg_nonneg.mpr hyn.le
    have hθ0 : 0 ≤ θ := le_trans (by norm_num) hθ
    have hmin : 0 ≤ min (-y) (1 : ℝ) :=
      le_min hnonneg (by norm_num)
    have hb := discounted_jump_compensator_bound θ (-y) hθ hnonneg
    have heq : -θ * (-y) = θ * y := by ring
    rw [heq] at hb
    have hle : 1 - Real.exp (θ * y) ≤ θ * min (-y) 1 := by
      simpa only [mul_comm] using (div_le_iff₀ hθpos).mp hb.2
    have hexp : Real.exp (θ * y) ≤ 1 :=
      Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonneg_of_nonpos hθ0 hyn.le)
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonpos (by linarith),
      abs_of_nonneg (mul_nonneg hθ0 hmin)]
    linarith
  exact Integrable.mono (hg.const_mul θ) (by fun_prop) hmajor
