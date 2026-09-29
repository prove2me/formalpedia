-- Prove2me | solution 1 for CelestialHolography.lorentzOfSL2C_hom
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T20:03:31.577834+00:00
-- url     : https://prove2.me/submissions/74cc0bec-d23f-4cf0-95eb-d3e5c3e9ed4b

import Mathlib
import Definitions.Def_CelestialHolography_LorentzMobius_Defs

set_option autoImplicit false

open CelestialHolography in
theorem celHol_toHermitian_isHermitian (x : Fin 4 → ℝ) :
    (toHermitian x).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [toHermitian]

open CelestialHolography in
theorem celHol_from_to (x : Fin 4 → ℝ) : fromHermitian (toHermitian x) = x := by
  funext i
  fin_cases i <;> simp [fromHermitian, toHermitian]

open CelestialHolography in
theorem celHol_to_from (X : Matrix (Fin 2) (Fin 2) ℂ) (hX : X.IsHermitian) :
    toHermitian (fromHermitian X) = X := by
  have h00 : star (X 0 0) = X 0 0 := hX.apply 0 0
  have h11 : star (X 1 1) = X 1 1 := hX.apply 1 1
  have h10 : star (X 0 1) = X 1 0 := hX.apply 1 0
  have h00' : (X 0 0).im = 0 := by
    have := congrArg Complex.im h00
    simp at this
    linarith
  have h11' : (X 1 1).im = 0 := by
    have := congrArg Complex.im h11
    simp at this
    linarith
  have h10re : (X 1 0).re = (X 0 1).re := by
    have := congrArg Complex.re h10
    simp at this
    linarith
  have h10im : (X 1 0).im = -(X 0 1).im := by
    have := congrArg Complex.im h10
    simp at this
    linarith
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [toHermitian, fromHermitian] <;> linarith

open CelestialHolography in
theorem solution (M N : Matrix.SpecialLinearGroup (Fin 2) ℂ) (x : Fin 4 → ℝ) :
    lorentzOfSL2C (M * N) x = lorentzOfSL2C M (lorentzOfSL2C N x) ∧
    lorentzOfSL2C 1 x = x := by
  constructor
  · unfold lorentzOfSL2C
    rw [celHol_to_from _ (Matrix.isHermitian_mul_mul_conjTranspose _
      (celHol_toHermitian_isHermitian x))]
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  · unfold lorentzOfSL2C
    rw [Matrix.SpecialLinearGroup.coe_one, Matrix.conjTranspose_one, Matrix.one_mul,
      Matrix.mul_one]
    exact celHol_from_to x
