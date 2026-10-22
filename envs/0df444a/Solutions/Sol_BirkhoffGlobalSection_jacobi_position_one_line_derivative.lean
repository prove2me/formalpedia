-- Prove2me | solution 1 for BirkhoffGlobalSection.jacobi_position_one_line_derivative
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T23:05:02.78699+00:00
-- url     : https://prove2.me/submissions/8aa82a82-712d-4591-84ac-22466b55b5f6

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
    HasDerivAt (fun t : ℝ => jacobiHamiltonian μ (Function.update s 0 t))
      (s 3 + (1 - μ) * (s 0 + μ) /
        (Real.sqrt ((s 0 + μ) ^ 2 + (s 1) ^ 2)) ^ 3 +
        μ * (s 0 - 1 + μ) /
        (Real.sqrt ((s 0 - 1 + μ) ^ 2 + (s 1) ^ 2)) ^ 3) (s 0) := by
  have hinv (a b x : ℝ) (hpos : 0 < (x + a) ^ 2 + b ^ 2) :
      HasDerivAt (fun t : ℝ => (Real.sqrt ((t + a) ^ 2 + b ^ 2))⁻¹)
        (-(x + a) / (Real.sqrt ((x + a) ^ 2 + b ^ 2)) ^ 3) x := by
    have hpoly : HasDerivAt (fun t : ℝ => (t + a) ^ 2 + b ^ 2)
        (2 * (x + a)) x := by
      convert! (((hasDerivAt_id (x := x)).add_const a).pow 2).add_const (b ^ 2)
        using 1 <;> norm_num
    have hroot : Real.sqrt ((x + a) ^ 2 + b ^ 2) ≠ 0 :=
      (Real.sqrt_pos.2 hpos).ne'
    have hraw := (hpoly.sqrt hpos.ne').inv hroot
    have hcoef : -(2 * (x + a) / (2 * Real.sqrt ((x + a) ^ 2 + b ^ 2))) /
        Real.sqrt ((x + a) ^ 2 + b ^ 2) ^ 2 =
        -(x + a) / Real.sqrt ((x + a) ^ 2 + b ^ 2) ^ 3 := by
      field_simp
    convert! hraw.congr_deriv hcoef using 1
  rcases hfree with ⟨h₁, h₂⟩
  have hleft := hinv μ (s 1) (s 0) h₁
  have h₂' : 0 < (s 0 + (μ - 1)) ^ 2 + (s 1) ^ 2 := by
    convert h₂ using 1 <;> ring
  have hright₀ := hinv (μ - 1) (s 1) (s 0) h₂'
  have hright : HasDerivAt
      (fun t : ℝ => (Real.sqrt ((t - 1 + μ) ^ 2 + (s 1) ^ 2))⁻¹)
      (-(s 0 - 1 + μ) / (Real.sqrt ((s 0 - 1 + μ) ^ 2 + (s 1) ^ 2)) ^ 3)
      (s 0) := by
    simpa only [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hright₀
  let C : ℝ := ((s 2) ^ 2 + (s 3) ^ 2) / 2 - s 1 * s 2
  have hfun : (fun t : ℝ => jacobiHamiltonian μ (Function.update s 0 t)) =
      (fun t : ℝ => (s 3) * t + C - (1 - μ) *
        (Real.sqrt ((t + μ) ^ 2 + (s 1) ^ 2))⁻¹ - μ *
        (Real.sqrt ((t - 1 + μ) ^ 2 + (s 1) ^ 2))⁻¹) := by
    funext t
    simp [C, jacobiHamiltonian, Function.update_apply, div_eq_mul_inv]
    ring
  rw [hfun]
  have hlinear := ((hasDerivAt_id (x := s 0)).const_mul (s 3)).add_const C
  have htotal := (hlinear.sub (hleft.const_mul (1 - μ))).sub
    (hright.const_mul μ)
  convert htotal using 1 <;> first | rfl | (funext t; ring) |
    (simp only [div_eq_mul_inv]; ring)
