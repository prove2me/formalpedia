-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_record_discount_smooth_height
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T17:29:19.639337+00:00
-- url     : https://prove2.me/submissions/021ac81c-6304-48b5-808e-b3735d2ec931

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_exp_log_scale_deriv
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

/-- Original-process discounted first-record survival is smooth
of all orders in the positive height parameter. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (a : ℝ) (ha : 0 < a) :
    ContDiffOn ℝ ⊤ (fun h : ℝ =>
      (∫⁻ ω, if twoSidedExitUpTime X h ω <
                  barrierRuinTime X a ω then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
      else 0 ∂P).toReal) (Ioi 0) := by
  let k : ℝ := deriv W a / W a
  have hlin : ContDiff ℝ ⊤ (fun h : ℝ => -(h * k)) :=
    (contDiff_id.mul contDiff_const).neg
  have hsmooth : ContDiffOn ℝ ⊤
      (fun h : ℝ => Real.exp (-(h * k))) (Ioi 0) :=
    (Real.contDiff_exp.comp hlin).contDiffOn
  apply hsmooth.congr
  intro h hh
  exact avram_wave4_01_original_record_discount_exp_log_scale_deriv
    X q hq W hW hvar a h ha hh
