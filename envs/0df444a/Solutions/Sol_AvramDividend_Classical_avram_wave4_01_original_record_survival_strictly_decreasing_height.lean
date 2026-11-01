-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_record_survival_strictly_decreasing_height
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T19:35:09.937837+00:00
-- url     : https://prove2.me/submissions/648f49a6-dd17-4bfa-abdc-b1b9d28ebc6b

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_exp_log_scale_deriv
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_log_slope_ge_positive_esscher_root
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

/-- Genuine killed first-record discounted survival is strictly decreasing
in the positive record height under the positive Esscher-root hypothesis. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (a : ℝ) (ha : 0 < a) :
    StrictAntiOn (fun h : ℝ =>
      (∫⁻ ω, if twoSidedExitUpTime X h ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitUpTime X h ω).toReal)))
      else 0 ∂P).toReal) (Ioi 0) := by
  have hκ : φ ≤ deriv W a / W a :=
    avram_wave4_01_original_record_log_slope_ge_positive_esscher_root
      X q hq W hW hvar φ hφ hroot a ha
  have hκpos : 0 < deriv W a / W a := lt_of_lt_of_le hφ hκ
  intro h₁ hh₁ h₂ hh₂ hlt
  dsimp only
  rw [avram_wave4_01_original_record_discount_exp_log_scale_deriv
      X q hq W hW hvar a h₁ ha hh₁,
    avram_wave4_01_original_record_discount_exp_log_scale_deriv
      X q hq W hW hvar a h₂ ha hh₂]
  exact Real.exp_lt_exp.mpr
    (neg_lt_neg (mul_lt_mul_of_pos_right hlt hκpos))
