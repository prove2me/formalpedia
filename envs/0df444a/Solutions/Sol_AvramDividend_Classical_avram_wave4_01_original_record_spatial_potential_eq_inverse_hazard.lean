-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_record_spatial_potential_eq_inverse_hazard
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T15:39:49.531576+00:00
-- url     : https://prove2.me/submissions/fc6a22c2-6102-453c-8162-5825269ed7ed

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
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

/-- The spatial potential of actual killed discounted strict records equals the reciprocal source hazard. -/
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
    (∫ h : ℝ in Ioi 0,
      (∫⁻ ω, if twoSidedExitUpTime X h ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitUpTime X h ω).toReal)))
      else 0 ∂P).toReal) =
    (deriv W a / W a)⁻¹ := by
  let k : ℝ := deriv W a / W a
  let F : ℝ → ℝ := fun h =>
    (∫⁻ ω, if twoSidedExitUpTime X h ω < barrierRuinTime X a ω then
      ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
    else 0 ∂P).toReal
  have hkle : φ ≤ k :=
    avram_wave4_01_original_record_log_slope_ge_positive_esscher_root
      X q hq W hW hvar φ hφ hroot a ha
  have hkpos : 0 < k := lt_of_lt_of_le hφ hkle
  have hkneg : -k < 0 := by linarith
  have hexp : (∫ h : ℝ in Ioi 0, Real.exp ((-k) * h)) = k⁻¹ := by
    rw [integral_exp_mul_Ioi hkneg 0]
    simp [hkpos.ne']
  have hcongr : (∫ h : ℝ in Ioi 0, F h) =
      (∫ h : ℝ in Ioi 0, Real.exp ((-k) * h)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro h hh
    have hhpos : 0 < h := hh
    have hE := avram_wave4_01_original_record_discount_exp_log_scale_deriv
      X q hq W hW hvar a h ha hhpos
    change F h = Real.exp (-(h * k)) at hE
    calc
      F h = Real.exp (-(h * k)) := hE
      _ = Real.exp ((-k) * h) := by congr 1; ring
  exact hcongr.trans hexp
