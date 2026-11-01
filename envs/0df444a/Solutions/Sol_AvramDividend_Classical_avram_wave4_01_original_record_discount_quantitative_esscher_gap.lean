-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_record_discount_quantitative_esscher_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T15:49:57.306514+00:00
-- url     : https://prove2.me/submissions/acfde5bd-8c43-45b3-9545-19fc17f781ad

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

/-- Genuine finite-depth record discount lies within height times hazard excess of unrestricted survival. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (a h : ℝ) (ha : 0 < a) (hh : 0 < h) :
    0 ≤ Real.exp (-(h * φ)) -
      (∫⁻ ω, if twoSidedExitUpTime X h ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitUpTime X h ω).toReal)))
      else 0 ∂P).toReal ∧
    Real.exp (-(h * φ)) -
      (∫⁻ ω, if twoSidedExitUpTime X h ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitUpTime X h ω).toReal)))
      else 0 ∂P).toReal ≤
      h * (deriv W a / W a - φ) := by
  let k : ℝ := deriv W a / W a
  have hkle : φ ≤ k :=
    avram_wave4_01_original_record_log_slope_ge_positive_esscher_root
      X q hq W hW hvar φ hφ hroot a ha
  have hd : 0 ≤ k - φ := sub_nonneg.mpr hkle
  have hdprod : 0 ≤ h * (k - φ) := mul_nonneg (le_of_lt hh) hd
  have hphi0 : -(h * φ) ≤ 0 := by nlinarith [mul_nonneg (le_of_lt hh) (le_of_lt hφ)]
  have htheta0 : -(h * (k - φ)) ≤ 0 := by linarith
  have hEphi : Real.exp (-(h * φ)) ≤ 1 := by
    simpa using (Real.exp_le_exp.mpr hphi0 :
      Real.exp (-(h * φ)) ≤ Real.exp 0)
  have hEtail : Real.exp (-(h * (k - φ))) ≤ 1 := by
    simpa using (Real.exp_le_exp.mpr htheta0 :
      Real.exp (-(h * (k - φ))) ≤ Real.exp 0)
  have hT : 0 ≤ 1 - Real.exp (-(h * (k - φ))) := by linarith
  have hTan : 1 - Real.exp (-(h * (k - φ))) ≤ h * (k - φ) := by
    have ht := Real.add_one_le_exp (-(h * (k - φ)))
    linarith
  have hsplit : Real.exp (-(h * k)) =
      Real.exp (-(h * φ)) * Real.exp (-(h * (k - φ))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hlinear : Real.exp (-(h * φ)) - Real.exp (-(h * k)) ≤
      h * (k - φ) := by
    rw [hsplit]
    have hm := mul_le_mul_of_nonneg_right hEphi hT
    nlinarith
  have hnonneg : 0 ≤ Real.exp (-(h * φ)) - Real.exp (-(h * k)) := by
    apply sub_nonneg.mpr
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (le_of_lt hh) hd]
  have hE := avram_wave4_01_original_record_discount_exp_log_scale_deriv
    X q hq W hW hvar a h ha hh
  rw [hE]
  exact ⟨hnonneg, hlinear⟩
