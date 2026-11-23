-- Prove2me | solution 1 for BLTCounting.AccuracySpace.equation_19
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:14:41.835615+00:00
-- url     : https://prove2.me/submissions/511ab1f5-3796-46c1-8400-3a9d3f3ffe26
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BLTCounting_AccuracySpace_FourierKernel
import Theorems.Thm_BLTCounting_AccuracySpace_lemma_2_8

open Complex MeasureTheory BLTCounting.AccuracySpace

namespace AuxEq19

lemma c0_two_mul (t : ℝ) :
    c0 (2 * t) = (Real.sqrt (2 * Real.pi))⁻¹ * Real.cosh t ^ (-(1 / 2 : ℝ)) := by
  unfold c0
  have h2 : (2 * t) / 2 = t := by ring
  rw [h2]
  congr 1
  have hpos : 0 < Real.cosh t := Real.cosh_pos t
  rw [one_div, Real.sqrt_inv, Real.sqrt_eq_rpow, Real.rpow_neg hpos.le]

end AuxEq19

theorem solution (ω : ℝ) :
    c0Hat ω = ((‖Complex.Gamma (1 / 4 + I * ω)‖ ^ 2 / Real.pi : ℝ) : ℂ) := by
  have h28 := lemma_2_8 (1 / 2) (2 * ω) (by norm_num)
  have hsub : c0Hat ω = ((2 : ℝ) : ℂ) *
      ∫ t : ℝ, ((c0 (2 * t) : ℝ) : ℂ) * cexp (-(I * (ω : ℂ) * ((2 * t : ℝ) : ℂ))) := by
    unfold c0Hat
    have hcomp := Measure.integral_comp_mul_left
      (fun x : ℝ => (c0 x : ℂ) * cexp (-(I * (ω : ℂ) * (x : ℂ)))) (2 : ℝ)
    have hinv : |(2 : ℝ)⁻¹| = (1 / 2 : ℝ) := by norm_num
    rw [hinv, Complex.real_smul] at hcomp
    have hmul := congrArg (fun z : ℂ => ((2 : ℝ) : ℂ) * z) hcomp
    dsimp at hmul
    calc
      (∫ x : ℝ, (c0 x : ℂ) * cexp (-(I * (ω : ℂ) * (x : ℂ))))
          = ((2 : ℝ) : ℂ) * ((((1 / 2 : ℝ) : ℂ)) *
              ∫ x : ℝ, (c0 x : ℂ) * cexp (-(I * (ω : ℂ) * (x : ℂ)))) := by
            rw [← mul_assoc]
            norm_num
      _ = ((2 : ℝ) : ℂ) *
          ∫ t : ℝ, ((c0 (2 * t) : ℝ) : ℂ) * cexp (-(I * (ω : ℂ) * ((2 * t : ℝ) : ℂ))) :=
        hmul.symm
  have hrew_int : (∫ t : ℝ, ((c0 (2 * t) : ℝ) : ℂ) * cexp (-(I * (ω : ℂ) * ((2 * t : ℝ) : ℂ)))) =
      (((Real.sqrt (2 * Real.pi))⁻¹ : ℝ) : ℂ) *
        ∫ t : ℝ, ((Real.cosh t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          cexp (-(I * ((2 * ω : ℝ) : ℂ) * (t : ℂ))) := by
    have hfun : (fun t : ℝ => ((c0 (2 * t) : ℝ) : ℂ) *
        cexp (-(I * (ω : ℂ) * ((2 * t : ℝ) : ℂ)))) =
        fun t : ℝ => (((Real.sqrt (2 * Real.pi))⁻¹ : ℝ) : ℂ) *
          (((Real.cosh t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            cexp (-(I * ((2 * ω : ℝ) : ℂ) * (t : ℂ)))) := by
      ext t
      rw [AuxEq19.c0_two_mul t]
      push_cast
      ring
    rw [hfun, integral_const_mul]
  rw [hsub, hrew_int, h28]
  have harg1 : (((1 / 2 : ℝ) : ℂ) + I * ((2 * ω : ℝ) : ℂ)) / 2 = 1 / 4 + I * (ω : ℂ) := by
    push_cast
    ring
  have harg2 : (((1 / 2 : ℝ) : ℂ) - I * ((2 * ω : ℝ) : ℂ)) / 2 =
      (starRingEnd ℂ) (1 / 4 + I * (ω : ℂ)) := by
    simp only [map_add, map_div₀, map_one, map_ofNat, map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring
  rw [harg1, harg2, Complex.Gamma_conj]
  have hprod_gamma : Complex.Gamma (1 / 4 + I * (ω : ℂ)) *
      (starRingEnd ℂ) (Complex.Gamma (1 / 4 + I * (ω : ℂ))) =
      ((‖Complex.Gamma (1 / 4 + I * (ω : ℂ))‖ ^ 2 : ℝ) : ℂ) := by
    simpa using Complex.mul_conj' (Complex.Gamma (1 / 4 + I * (ω : ℂ)))
  have hpre : 2 * (Real.sqrt (2 * Real.pi))⁻¹ *
      ((2 : ℝ) ^ ((1 / 2 : ℝ) - 1) / Real.Gamma (1 / 2)) = 1 / Real.pi := by
    rw [Real.Gamma_one_half_eq]
    have hrpow : (2 : ℝ) ^ ((1 / 2 : ℝ) - 1) = (Real.sqrt 2)⁻¹ := by
      rw [show (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) by norm_num,
        Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
    rw [hrpow, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hs2 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    have hspi : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
    field_simp [hs2, hspi, ne_of_gt Real.pi_pos]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sq_sqrt Real.pi_pos.le]
  calc
    ((2 : ℝ) : ℂ) * ((((Real.sqrt (2 * Real.pi))⁻¹ : ℝ) : ℂ) *
      (((((2 : ℝ) ^ ((1 / 2 : ℝ) - 1) / Real.Gamma (1 / 2) : ℝ) : ℂ) *
        Complex.Gamma (1 / 4 + I * (ω : ℂ)) *
        (starRingEnd ℂ) (Complex.Gamma (1 / 4 + I * (ω : ℂ))))))
        = (((2 * (Real.sqrt (2 * Real.pi))⁻¹ *
            ((2 : ℝ) ^ ((1 / 2 : ℝ) - 1) / Real.Gamma (1 / 2)) : ℝ) : ℂ) *
          (Complex.Gamma (1 / 4 + I * (ω : ℂ)) *
            (starRingEnd ℂ) (Complex.Gamma (1 / 4 + I * (ω : ℂ))))) := by
          push_cast
          ring
    _ = (((1 / Real.pi : ℝ) : ℂ) * ((‖Complex.Gamma (1 / 4 + I * (ω : ℂ))‖ ^ 2 : ℝ) : ℂ)) := by
      rw [hpre, hprod_gamma]
    _ = ((‖Complex.Gamma (1 / 4 + I * (ω : ℂ))‖ ^ 2 / Real.pi : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul]
      congr 1
      ring
