-- Prove2me | solution 1 for AvramDividend.Classical.p2m81_bv_J_mono_no_standing_public
-- status  : ACCEPTED   (prove)
-- author  : @RSoulat
-- created : 2026-11-22T14:16:34.093353+00:00
-- url     : https://prove2.me/submissions/46dea615-a751-414e-8bbf-670193aa8b34

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_compensated_jump_integrable_nonneg

open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal

set_option autoImplicit false

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) :
    ∀ θ₁ θ₂ : ℝ, 0 < θ₁ → θ₁ ≤ θ₂ →
      (∫ y : ℝ, (Real.exp (θ₁ * y) - 1 - θ₁ * y) / θ₁ ∂(X.ν.restrict (Ioo (-1 : ℝ) 0))) ≤
      (∫ y : ℝ, (Real.exp (θ₂ * y) - 1 - θ₂ * y) / θ₂ ∂(X.ν.restrict (Ioo (-1 : ℝ) 0))) := by
  intro θ₁ θ₂ h₁ h₁₂
  have h₂ := h₁.trans_le h₁₂
  have hInt (θ : ℝ) (hθ : 0 < θ) : IntegrableOn
      (fun y : ℝ => (Real.exp (θ * y) - 1 - θ * y) / θ) (Ioo (-1 : ℝ) 0) X.ν := by
    have hRaw := (levy_compensated_jump_integrable_nonneg X θ hθ.le).mono_set
      (show Ioo (-1 : ℝ) 0 ⊆ Iio 0 from fun _ hy => hy.2)
    have hComp : IntegrableOn (fun y : ℝ => Real.exp (θ * y) - 1 - θ * y)
        (Ioo (-1 : ℝ) 0) X.ν := by
      exact hRaw.congr_fun (fun y hy => by
        have hy' : y ∈ Ioo (-1 : ℝ) 1 := ⟨hy.1, hy.2.trans zero_lt_one⟩
        simp [Set.indicator_of_mem hy']) measurableSet_Ioo
    exact hComp.div_const θ
  apply integral_mono (hInt θ₁ h₁) (hInt θ₂ h₂)
  intro y
  have hc : ConvexOn ℝ univ (fun θ : ℝ => Real.exp (θ * y)) := by
    simpa [Function.comp_def, mul_comm] using
      (convexOn_exp.comp_linearMap (LinearMap.mul ℝ ℝ y))
  have hslope := hc.secant_mono (a := 0) (x := θ₁) (y := θ₂)
    (mem_univ _) (mem_univ _) (mem_univ _) h₁.ne' h₂.ne' h₁₂
  simp only [zero_mul, Real.exp_zero, sub_zero] at hslope
  simpa only [sub_div, mul_div_cancel_left₀ _ h₁.ne', mul_div_cancel_left₀ _ h₂.ne'] using
    sub_le_sub_right hslope y
