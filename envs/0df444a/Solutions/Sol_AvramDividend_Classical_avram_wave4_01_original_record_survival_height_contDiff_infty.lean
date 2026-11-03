-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_record_survival_height_contDiff_infty
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T07:35:31.85397+00:00
-- url     : https://prove2.me/submissions/cbdf0e8d-de8d-438e-a09a-276cc974cd61

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
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitUpTime X h ω).toReal)))
      else 0 ∂P).toReal) (Ioi 0) := by
  have hsmooth : ContDiff ℝ ⊤
      (fun h : ℝ => Real.exp (-(h * (deriv W a / W a)))) := by
    exact Real.contDiff_exp.comp
      ((contDiff_id.mul contDiff_const).neg)
  apply hsmooth.contDiffOn.congr
  intro h hh
  exact avram_wave4_01_original_record_discount_exp_log_scale_deriv
    X q hq W hW hvar a h ha hh
