-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18p1a1b_large_exp_lintegral_real_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T02:16:16.43463+00:00
-- url     : https://prove2.me/submissions/aeab8ba5-4c3b-46b5-860e-c269c5482478

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_large_negative_jump_unit_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Nonnegative original large negative exponential loss equals its real signed integral. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 < θ) :
    (∫⁻ z in Iic (-1 : ℝ),
      ENNReal.ofReal ((1 - Real.exp (θ * z)) / θ) ∂X.ν) =
      ENNReal.ofReal
        (- (∫ z in Iic (-1 : ℝ), (Real.exp (θ * z) - 1) ∂X.ν) / θ) := by
  let B : Set ℝ := Iic (-1 : ℝ)
  let f : ℝ → ℝ := fun z => (1 - Real.exp (θ * z)) / θ
  have hBounds (z : ℝ) (hz : z ∈ B) :
      0 ≤ f z ∧ f z ≤ 1 / θ := by
    have hz0 : z ≤ 0 := hz.trans (by norm_num)
    have hprod : θ * z ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hθ.le hz0
    have hexp : Real.exp (θ * z) ≤ 1 :=
      (Real.exp_le_one_iff).2 hprod
    have hexp0 : 0 ≤ Real.exp (θ * z) := (Real.exp_pos _).le
    dsimp [f]
    constructor
    · exact div_nonneg (sub_nonneg.mpr hexp) hθ.le
    · apply (div_le_div_iff₀ hθ hθ).2
      nlinarith
  have hOne : IntegrableOn (fun _ : ℝ => (1 : ℝ)) B X.ν := by
    simpa only [B] using levy_large_negative_jump_unit_integrable X
  have hConst : IntegrableOn (fun _ : ℝ => 1 / θ) B X.ν := by
    simpa only [IntegrableOn, mul_one] using (hOne.const_mul (1 / θ))
  have hFInt : IntegrableOn f B X.ν := by
    apply hConst.mono' (by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Iic] with z hz
    have hb := hBounds z hz
    simpa only [Real.norm_eq_abs, abs_of_nonneg hb.1,
      abs_of_nonneg (one_div_nonneg.mpr hθ.le)] using hb.2
  have hNonneg : 0 ≤ᵐ[X.ν.restrict B] f := by
    filter_upwards [ae_restrict_mem measurableSet_Iic] with z hz
    exact (hBounds z hz).1
  have hReal :
      (∫ z in B, f z ∂X.ν) =
        - (∫ z in B, Real.exp (θ * z) - 1 ∂X.ν) / θ := by
    calc
      (∫ z in B, f z ∂X.ν) =
          (∫ z in B, -(Real.exp (θ * z) - 1) ∂X.ν) / θ := by
        calc
          (∫ z in B, f z ∂X.ν) =
              (∫ z in B, (-(Real.exp (θ * z) - 1)) * θ⁻¹ ∂X.ν) := by
            apply integral_congr_ae
            filter_upwards [] with z
            dsimp [f]
            ring
          _ = (∫ z in B, -(Real.exp (θ * z) - 1) ∂X.ν) * θ⁻¹ :=
            integral_mul_const θ⁻¹ (fun z : ℝ => -(Real.exp (θ * z) - 1))
          _ = (∫ z in B, -(Real.exp (θ * z) - 1) ∂X.ν) / θ := by
            ring
      _ = - (∫ z in B, Real.exp (θ * z) - 1 ∂X.ν) / θ := by
        rw [integral_neg]
  calc
    (∫⁻ z in B, ENNReal.ofReal (f z) ∂X.ν) =
        ENNReal.ofReal (∫ z in B, f z ∂X.ν) := by
      exact (ofReal_integral_eq_lintegral_ofReal hFInt hNonneg).symm
    _ = ENNReal.ofReal
        (- (∫ z in B, Real.exp (θ * z) - 1 ∂X.ν) / θ) := by
      rw [hReal]
