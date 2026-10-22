-- Prove2me | solution 1 for BirkhoffGlobalSection.jacobi_position_two_line_derivative
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T23:00:15.515988+00:00
-- url     : https://prove2.me/submissions/f75087ea-ba49-41cf-8212-f3eb7930ad63

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_BirkhoffGlobalSection

open BirkhoffGlobalSection

theorem solution (μ : ℝ) (s : Phase)
    (hfree : collisionFree μ s) :
    HasDerivAt (fun t : ℝ => jacobiHamiltonian μ (Function.update s 1 t))
      (-s 2 + (1 - μ) * (s 1) /
        (Real.sqrt ((s 0 + μ) ^ 2 + (s 1) ^ 2)) ^ 3 +
        μ * (s 1) /
        (Real.sqrt ((s 0 - 1 + μ) ^ 2 + (s 1) ^ 2)) ^ 3) (s 1) := by
  have hinv (a b : ℝ) (hpos : 0 < a ^ 2 + b ^ 2) :
      HasDerivAt (fun t : ℝ => (Real.sqrt (a ^ 2 + t ^ 2))⁻¹)
        (-b / (Real.sqrt (a ^ 2 + b ^ 2)) ^ 3) b := by
    have hpoly : HasDerivAt (fun t : ℝ => a ^ 2 + t ^ 2) (2 * b) b := by
      convert! (hasDerivAt_pow 2 b).const_add (a ^ 2) using 1 <;>
        norm_num
    have hroot : Real.sqrt (a ^ 2 + b ^ 2) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
    have hraw := (hpoly.sqrt hpos.ne').inv hroot
    have hcoef : -(2 * b / (2 * Real.sqrt (a ^ 2 + b ^ 2))) /
        Real.sqrt (a ^ 2 + b ^ 2) ^ 2 =
        -b / Real.sqrt (a ^ 2 + b ^ 2) ^ 3 := by
      field_simp
    convert! hraw.congr_deriv hcoef using 1
  rcases hfree with ⟨h₁, h₂⟩
  have hleft := hinv (s 0 + μ) (s 1) h₁
  have hright := hinv (s 0 - 1 + μ) (s 1) h₂
  let C : ℝ := ((s 2) ^ 2 + (s 3) ^ 2) / 2 + s 0 * s 3
  have hfun : (fun t : ℝ => jacobiHamiltonian μ (Function.update s 1 t)) =
      (fun t : ℝ => -(s 2) * t + C - (1 - μ) *
        (Real.sqrt ((s 0 + μ) ^ 2 + t ^ 2))⁻¹ - μ *
        (Real.sqrt ((s 0 - 1 + μ) ^ 2 + t ^ 2))⁻¹) := by
    funext t
    simp [C, jacobiHamiltonian, Function.update_apply, div_eq_mul_inv]
    ring
  rw [hfun]
  have hlinear := ((hasDerivAt_id (x := s 1)).const_mul (-(s 2))).add_const C
  have htotal := (hlinear.sub (hleft.const_mul (1 - μ))).sub
    (hright.const_mul μ)
  convert htotal using 1 <;> first | rfl | (funext t; ring) |
    (simp only [div_eq_mul_inv]; ring)
