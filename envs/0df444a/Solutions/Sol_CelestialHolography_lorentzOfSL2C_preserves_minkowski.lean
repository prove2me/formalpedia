-- Prove2me | solution 1 for CelestialHolography.lorentzOfSL2C_preserves_minkowski
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-28T22:41:53.924366+00:00
-- url     : https://prove2.me/submissions/13873cd6-ebf0-4539-9922-5a8aff8e30da

import Mathlib
import Definitions.Def_CelestialHolography_LorentzMobius_Defs

open CelestialHolography

lemma mink_fromHermitian (Y : Matrix (Fin 2) (Fin 2) ℂ) (hY : Y.IsHermitian) :
    minkowskiNormSq (fromHermitian Y) = -(Y.det).re := by
  have h00 : (Y 0 0).im = 0 := by
    have h := congrArg Complex.im (hY.apply 0 0)
    simp at h
    linarith
  have h11 : (Y 1 1).im = 0 := by
    have h := congrArg Complex.im (hY.apply 1 1)
    simp at h
    linarith
  have h10 : Y 1 0 = star (Y 0 1) := (hY.apply 1 0).symm
  rw [Matrix.det_fin_two, h10]
  simp [minkowskiNormSq, fromHermitian, Complex.mul_re, h00, h11]
  ring

lemma mink_toHermitian (x : Fin 4 → ℝ) :
    minkowskiNormSq x = -((toHermitian x).det).re := by
  simp [toHermitian, Matrix.det_fin_two, minkowskiNormSq, Complex.mul_re]
  ring

theorem solution (M : Matrix.SpecialLinearGroup (Fin 2) ℂ)
    (x : Fin 4 → ℝ) : minkowskiNormSq (lorentzOfSL2C M x) = minkowskiNormSq x := by
  unfold lorentzOfSL2C
  have hX : (toHermitian x).IsHermitian := by
    unfold Matrix.IsHermitian
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [toHermitian, Matrix.conjTranspose_apply, Complex.ext_iff]
  have hY : ((M : Matrix (Fin 2) (Fin 2) ℂ) * toHermitian x *
      Matrix.conjTranspose (M : Matrix (Fin 2) (Fin 2) ℂ)).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hX.eq, Matrix.mul_assoc]
  rw [mink_fromHermitian _ hY, mink_toHermitian x, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_conjTranspose, Matrix.SpecialLinearGroup.det_coe, star_one, one_mul, mul_one]
