-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_record_weighted_esscher_height_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T19:13:53.438734+00:00
-- url     : https://prove2.me/submissions/1b5df798-dd86-45cc-b734-f13049d821c4

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

/-- The actual killed first-record discounted spatial density is integrable
over all positive record heights at every tilt θ > -φ. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (a θ : ℝ) (ha : 0 < a) (hθ : -φ < θ) :
    IntegrableOn (fun h : ℝ =>
      Real.exp (-(θ * h)) *
        (∫⁻ ω, if twoSidedExitUpTime X h ω <
            barrierRuinTime X a ω then
          ENNReal.ofReal (Real.exp (-(q *
            (twoSidedExitUpTime X h ω).toReal)))
        else 0 ∂P).toReal) (Ioi 0) := by
  let κ : ℝ := deriv W a / W a
  have hκ : φ ≤ κ :=
    avram_wave4_01_original_record_log_slope_ge_positive_esscher_root
      X q hq W hW hvar φ hφ hroot a ha
  have hneg : -(θ + κ) < 0 := by linarith
  have hint : IntegrableOn
      (fun h : ℝ => Real.exp ((-(θ + κ)) * h)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (a := -(θ + κ)) hneg 0
  apply hint.congr_fun _ measurableSet_Ioi
  intro h hh
  have hr := avram_wave4_01_original_record_discount_exp_log_scale_deriv
    X q hq W hW hvar a h ha hh
  change Real.exp ((-(θ + κ)) * h) =
    Real.exp (-(θ * h)) *
      (∫⁻ ω, if twoSidedExitUpTime X h ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitUpTime X h ω).toReal)))
      else 0 ∂P).toReal
  rw [hr]
  rw [← Real.exp_add]
  congr 1
  ring
