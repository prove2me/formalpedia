-- Prove2me | solution 1 for CarrollGR.spherical_coordinates_minkowski
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T12:24:22.139123+00:00
-- url     : https://prove2.me/submissions/0d037b83-d0c3-4088-b873-a990d2796841

import Mathlib
import Definitions.Def_CarrollGR_Defs

/-! 7249f9fa CarrollGR.spherical_coordinates_minkowski.
Compute the Jacobian of the spherical-coordinate map entrywise via explicit HasFDerivAt
terms built from coordinate projections, then expand Jᵀ η J and simplify with sin² + cos² = 1. -/

set_option autoImplicit false

open scoped ContDiff

namespace CGR7249

open CarrollGR

theorem jac_eq (x : Coord) :
    jacobian sphericalToCartesian x = Matrix.of ![
      ![1, 0, 0, 0],
      ![0, Real.sin (x 2) * Real.cos (x 3), x 1 * Real.cos (x 2) * Real.cos (x 3),
        -(x 1 * Real.sin (x 2) * Real.sin (x 3))],
      ![0, Real.sin (x 2) * Real.sin (x 3), x 1 * Real.cos (x 2) * Real.sin (x 3),
        x 1 * Real.sin (x 2) * Real.cos (x 3)],
      ![0, Real.cos (x 2), -(x 1 * Real.sin (x 2)), 0]] := by
  have p : ∀ i : Fin 4, HasFDerivAt (fun y : Coord => y i)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) i) x :=
    fun i => hasFDerivAt_apply i x
  have e0 : (fun y : Coord => sphericalToCartesian y 0) = fun y => y 0 := by
    funext y; simp [sphericalToCartesian]
  have e1 : (fun y : Coord => sphericalToCartesian y 1)
      = fun y => y 1 * Real.sin (y 2) * Real.cos (y 3) := by
    funext y; simp [sphericalToCartesian]
  have e2 : (fun y : Coord => sphericalToCartesian y 2)
      = fun y => y 1 * Real.sin (y 2) * Real.sin (y 3) := by
    funext y; simp [sphericalToCartesian]
  have e3 : (fun y : Coord => sphericalToCartesian y 3)
      = fun y => y 1 * Real.cos (y 2) := by
    funext y; simp [sphericalToCartesian]
  have h1 : HasFDerivAt (fun y : Coord => y 1 * Real.sin (y 2) * Real.cos (y 3)) _ x := ((p 1).mul (p 2).sin).mul (p 3).cos
  have h2 : HasFDerivAt (fun y : Coord => y 1 * Real.sin (y 2) * Real.sin (y 3)) _ x := ((p 1).mul (p 2).sin).mul (p 3).sin
  have h3 : HasFDerivAt (fun y : Coord => y 1 * Real.cos (y 2)) _ x := (p 1).mul (p 2).cos
  ext a μ
  fin_cases a
  · simp only [jacobian, partialD, Matrix.of_apply, Fin.zero_eta]
    rw [e0, (p 0).fderiv]
    fin_cases μ <;> simp
  · simp only [jacobian, partialD, Matrix.of_apply, Fin.mk_one]
    rw [e1, h1.fderiv]
    fin_cases μ <;> simp <;> ring
  · simp only [jacobian, partialD, Matrix.of_apply]
    rw [show ((⟨2, by decide⟩ : Fin 4)) = 2 from rfl, e2, h2.fderiv]
    fin_cases μ <;> simp <;> ring
  · simp only [jacobian, partialD, Matrix.of_apply]
    rw [show ((⟨3, by decide⟩ : Fin 4)) = 3 from rfl, e3, h3.fderiv]
    fin_cases μ <;> simp

end CGR7249

open CarrollGR in open scoped ContDiff in
theorem solution (x : Coord) :
    (jacobian sphericalToCartesian x).transpose * minkowskiEta * jacobian sphericalToCartesian x
      = sphericalMetric (fun _ _ => 1) (fun _ _ => 1) x := by
  rw [CGR7249.jac_eq]
  have hs := Real.sin_sq_add_cos_sq (x 2)
  have ht := Real.sin_sq_add_cos_sq (x 3)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sphericalMetric, minkowskiEta, Matrix.mul_apply, Fin.sum_univ_four,
      Matrix.diagonal_apply] <;>
    first
    | ring1
    | linear_combination Real.sin (x 2) ^ 2 * ht + hs
    | linear_combination Real.sin (x 2) * x 1 * Real.cos (x 2) * ht
    | linear_combination x 1 ^ 2 * Real.cos (x 2) ^ 2 * ht + x 1 ^ 2 * hs
    | linear_combination x 1 ^ 2 * Real.sin (x 2) ^ 2 * ht
