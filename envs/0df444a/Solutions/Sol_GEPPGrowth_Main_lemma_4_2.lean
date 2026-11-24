-- Prove2me | solution 1 for GEPPGrowth.Main.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T00:27:04.161688+00:00
-- url     : https://prove2.me/submissions/e69aaac4-fd05-4d5d-a87c-fafdaeed03c8

import Definitions.Def_GEPPGrowth_Main_Process

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

noncomputable section

open GEPPGrowth.Main

private lemma pdf_le (x : ℝ) :
    gaussianPDF 0 1 x ≤ ENNReal.ofReal (Real.sqrt (2 * Real.pi))⁻¹ := by
  unfold gaussianPDF gaussianPDFReal
  apply ENNReal.ofReal_le_ofReal
  have h1 : Real.exp (-(x - 0) ^ 2 / (2 * ((1 : NNReal) : ℝ))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ (x - 0) ^ 2 := sq_nonneg _
    have h2 : (0 : ℝ) < 2 * ((1 : NNReal) : ℝ) := by norm_num
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) h2.le
  have h3 : (0 : ℝ) ≤ (Real.sqrt (2 * Real.pi * ((1 : NNReal) : ℝ)))⁻¹ := by positivity
  calc (Real.sqrt (2 * Real.pi * ((1 : NNReal) : ℝ)))⁻¹ *
        Real.exp (-(x - 0) ^ 2 / (2 * ((1 : NNReal) : ℝ)))
      ≤ (Real.sqrt (2 * Real.pi * ((1 : NNReal) : ℝ)))⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left h1 h3
    _ = (Real.sqrt (2 * Real.pi))⁻¹ := by simp

private lemma const_eq (t : ℝ) :
    (Real.sqrt (2 * Real.pi))⁻¹ * (t - -t) = t * Real.sqrt (2 / Real.pi) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hsp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr hpi
  have hs2p : 0 < Real.sqrt 2 := by positivity
  rw [Real.sqrt_mul (by norm_num), Real.sqrt_div (by norm_num)]
  field_simp
  rw [Real.sq_sqrt (by norm_num)]
  ring

theorem solution (t : ℝ) (ht : 0 < t) :
    prob (gaussianReal 0 1) {x | |x| ≤ t} ≤ t * Real.sqrt (2 / Real.pi) := by
  have hset : {x : ℝ | |x| ≤ t} = Set.Icc (-t) t := by
    ext x; simp [abs_le]
  unfold prob
  rw [hset]
  apply ENNReal.toReal_le_of_le_ofReal (by positivity)
  rw [gaussianReal_apply 0 one_ne_zero]
  calc ∫⁻ x in Set.Icc (-t) t, gaussianPDF 0 1 x
      ≤ ∫⁻ _ in Set.Icc (-t) t, ENNReal.ofReal (Real.sqrt (2 * Real.pi))⁻¹ :=
        lintegral_mono (fun x => pdf_le x)
    _ = ENNReal.ofReal (Real.sqrt (2 * Real.pi))⁻¹ * ENNReal.ofReal (t - -t) := by
        rw [setLIntegral_const, Real.volume_Icc]
    _ = ENNReal.ofReal (t * Real.sqrt (2 / Real.pi)) := by
        rw [← ENNReal.ofReal_mul (by positivity), const_eq]
