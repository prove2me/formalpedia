-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_record_survival_height_hazard_ode
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T22:17:32.417448+00:00
-- url     : https://prove2.me/submissions/cecd66bc-9951-4527-acf5-350ae2094036

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_exp_log_scale_deriv
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology

/-- Genuine killed first-record survival obeys the exact
first-order hazard ODE in record height. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (a h : ℝ) (ha : 0 < a) (hh : 0 < h) :
    HasDerivAt (fun r : ℝ =>
      (∫⁻ ω, if twoSidedExitUpTime X r ω <
                  barrierRuinTime X a ω then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X r ω).toReal)))
      else 0 ∂P).toReal)
      ((∫⁻ ω, if twoSidedExitUpTime X h ω <
                  barrierRuinTime X a ω then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
      else 0 ∂P).toReal * (-(deriv W a / W a))) h := by
  let k : ℝ := deriv W a / W a
  let G : ℝ → ℝ := fun r =>
    (∫⁻ ω, if twoSidedExitUpTime X r ω < barrierRuinTime X a ω then
      ENNReal.ofReal
        (Real.exp (-(q * (twoSidedExitUpTime X r ω).toReal)))
    else 0 ∂P).toReal
  change HasDerivAt G (G h * (-k)) h
  have hExpEq (r : ℝ) (hr : 0 < r) :
      G r = Real.exp (r * (-k)) := by
    simpa only [mul_neg] using
      (avram_wave4_01_original_record_discount_exp_log_scale_deriv
        X q hq W hW hvar a r ha hr)
  have hlin : HasDerivAt (fun r : ℝ => r * (-k)) (-k) h :=
    hasDerivAt_mul_const (-k)
  have hexp : HasDerivAt (fun r : ℝ => Real.exp (r * (-k)))
      (Real.exp (h * (-k)) * (-k)) h := by
    simpa only [Function.comp_def] using hlin.exp
  have hEq : G =ᶠ[𝓝 h] (fun r : ℝ => Real.exp (r * (-k))) := by
    filter_upwards [isOpen_Ioi.mem_nhds hh] with r hr
    exact hExpEq r hr
  have hDeriv : HasDerivAt G (Real.exp (h * (-k)) * (-k)) h :=
    hexp.congr_of_eventuallyEq hEq
  simpa only [hExpEq h hh] using hDeriv
