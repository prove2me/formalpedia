-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_record_discount_height_ode
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T12:05:54.916663+00:00
-- url     : https://prove2.me/submissions/930d5768-b4f7-44c9-9709-9c135aee01b5

import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_exp_log_scale_deriv

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The genuine killed first-record discount solves the constant-coefficient
height-hazard ODE at every positive record level, without Standing. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤) :
    ∀ a h : ℝ, 0 < a → 0 < h →
      HasDerivAt
        (fun b : ℝ =>
          (∫⁻ ω, if twoSidedExitUpTime X b ω <
                      barrierRuinTime X a ω then
            ENNReal.ofReal
              (Real.exp (-(q * (twoSidedExitUpTime X b ω).toReal)))
          else 0 ∂P).toReal)
        (-(deriv W a / W a) *
          (∫⁻ ω, if twoSidedExitUpTime X h ω <
                      barrierRuinTime X a ω then
            ENNReal.ofReal
              (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
          else 0 ∂P).toReal) h := by
  intro a h ha hh
  let r : ℝ := deriv W a / W a
  let G : ℝ → ℝ := fun b =>
    (∫⁻ ω, if twoSidedExitUpTime X b ω <
                barrierRuinTime X a ω then
      ENNReal.ofReal
        (Real.exp (-(q * (twoSidedExitUpTime X b ω).toReal)))
    else 0 ∂P).toReal
  change HasDerivAt G (-r * G h) h
  have hFormula (b : ℝ) (hb : 0 < b) :
      G b = Real.exp (-(b * r)) := by
    simpa only [G, r] using
      (avram_wave4_01_original_record_discount_exp_log_scale_deriv
        X q hq W hW hvar a b ha hb)
  have hlin :
      HasDerivAt (fun b : ℝ => -(b * r)) (-r) h := by
    have hfun : (fun b : ℝ => -(b * r)) =
        (fun b : ℝ => (-r) * b) := by
      funext b
      ring
    rw [hfun]
    exact hasDerivAt_const_mul (-r)
  have hexp :
      HasDerivAt
        (fun b : ℝ => Real.exp (-(b * r)))
        (Real.exp (-(h * r)) * (-r)) h :=
    by simpa only [Function.comp_def] using
      ((Real.hasDerivAt_exp (-(h * r))).comp h hlin)
  have hnear :
      G =ᶠ[nhds h] (fun b : ℝ => Real.exp (-(b * r))) := by
    filter_upwards [isOpen_Ioi.mem_nhds hh] with b hb
    exact hFormula b hb
  have hG := hexp.congr_of_eventuallyEq hnear
  rw [← hFormula h hh] at hG
  simpa only [mul_comm] using hG
