-- Prove2me | solution 1 for CarrollGR.kruskal_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T20:30:29.086714+00:00
-- url     : https://prove2.me/submissions/14a68a09-99e5-4d4e-996b-a1adb5c26105

import Mathlib
import Definitions.Def_CarrollGR_Defs

/-! 879c20b2 CarrollGR.kruskal_coordinates.
Compute the Jacobian of (t,r,θ,φ) ↦ (v,u,θ,φ) entrywise via explicit HasFDerivAt terms,
then expand Jᵀ K J, generalize √(r/2Gm-1), the exponentials, cosh and sinh to atoms,
substitute r = 2Gm(S²+1), and close each entry by linear_combination + field_simp. -/

set_option autoImplicit false

open scoped ContDiff

namespace CGR879

open CarrollGR

theorem jac_eq (GN m : ℝ) (hGN : 0 < GN) (hm : 0 < m) (x : Coord) (hr : 2 * GN * m < x 1) :
    jacobian (schwarzschildToKruskal GN m) x = Matrix.of ![
      ![√(x 1 / (2 * GN * m) - 1) * Real.exp (x 1 / (4 * GN * m))
          * Real.cosh (x 0 / (4 * GN * m)) / (4 * GN * m),
        Real.exp (x 1 / (4 * GN * m)) * Real.sinh (x 0 / (4 * GN * m))
          * (1 / (4 * GN * m * √(x 1 / (2 * GN * m) - 1)) + √(x 1 / (2 * GN * m) - 1) / (4 * GN * m)),
        0, 0],
      ![√(x 1 / (2 * GN * m) - 1) * Real.exp (x 1 / (4 * GN * m))
          * Real.sinh (x 0 / (4 * GN * m)) / (4 * GN * m),
        Real.exp (x 1 / (4 * GN * m)) * Real.cosh (x 0 / (4 * GN * m))
          * (1 / (4 * GN * m * √(x 1 / (2 * GN * m) - 1)) + √(x 1 / (2 * GN * m) - 1) / (4 * GN * m)),
        0, 0],
      ![0, 0, 1, 0],
      ![0, 0, 0, 1]] := by
  have hc : 0 < 2 * GN * m := by positivity
  have hw : 0 < x 1 / (2 * GN * m) - 1 := by
    rw [sub_pos, one_lt_div hc]; exact hr
  have hS : 0 < √(x 1 / (2 * GN * m) - 1) := Real.sqrt_pos.mpr hw
  have hGN0 : GN ≠ 0 := hGN.ne'
  have hm0 : m ≠ 0 := hm.ne'
  have hS0 : √(x 1 / (2 * GN * m) - 1) ≠ 0 := hS.ne'
  have p : ∀ i : Fin 4, HasFDerivAt (fun y : Coord => y i)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) i) x :=
    fun i => hasFDerivAt_apply i x
  have hd : ∀ (i : Fin 4) (d : ℝ), HasFDerivAt (fun y : Coord => y i / d)
      (d⁻¹ • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) i) x := by
    intro i d
    rw [show (fun y : Coord => y i / d) = fun y => d⁻¹ * y i by funext y; ring]
    exact (p i).const_mul d⁻¹
  have e0 : (fun y : Coord => schwarzschildToKruskal GN m y 0)
      = fun y => √(y 1 / (2 * GN * m) - 1) * Real.exp (y 1 / (4 * GN * m))
          * Real.sinh (y 0 / (4 * GN * m)) := by
    funext y; simp [schwarzschildToKruskal, kruskalV]
  have e1 : (fun y : Coord => schwarzschildToKruskal GN m y 1)
      = fun y => √(y 1 / (2 * GN * m) - 1) * Real.exp (y 1 / (4 * GN * m))
          * Real.cosh (y 0 / (4 * GN * m)) := by
    funext y; simp [schwarzschildToKruskal, kruskalU]
  have e2 : (fun y : Coord => schwarzschildToKruskal GN m y 2) = fun y => y 2 := by
    funext y; simp [schwarzschildToKruskal]
  have e3 : (fun y : Coord => schwarzschildToKruskal GN m y 3) = fun y => y 3 := by
    funext y; simp [schwarzschildToKruskal]
  have hw' : HasFDerivAt (fun y : Coord => y 1 / (2 * GN * m) - 1) _ x :=
    (hd 1 (2 * GN * m)).sub_const 1
  have h0 : HasFDerivAt (fun y : Coord => √(y 1 / (2 * GN * m) - 1) * Real.exp (y 1 / (4 * GN * m))
          * Real.sinh (y 0 / (4 * GN * m))) _ x :=
    ((hw'.sqrt hw.ne').mul (hd 1 (4 * GN * m)).exp).mul
      (hd 0 (4 * GN * m)).sinh
  have h1 : HasFDerivAt (fun y : Coord => √(y 1 / (2 * GN * m) - 1) * Real.exp (y 1 / (4 * GN * m))
          * Real.cosh (y 0 / (4 * GN * m))) _ x :=
    ((hw'.sqrt hw.ne').mul (hd 1 (4 * GN * m)).exp).mul
      (hd 0 (4 * GN * m)).cosh
  ext a μ
  fin_cases a
  · simp only [jacobian, partialD, Matrix.of_apply, Fin.zero_eta]
    rw [e0, h0.fderiv]
    fin_cases μ <;> simp <;> field_simp <;> ring
  · simp only [jacobian, partialD, Matrix.of_apply, Fin.mk_one]
    rw [e1, h1.fderiv]
    fin_cases μ <;> simp <;> field_simp <;> ring
  · simp only [jacobian, partialD, Matrix.of_apply]
    rw [show ((⟨2, by decide⟩ : Fin 4)) = 2 from rfl, e2, (p 2).fderiv]
    fin_cases μ <;> simp
  · simp only [jacobian, partialD, Matrix.of_apply]
    rw [show ((⟨3, by decide⟩ : Fin 4)) = 3 from rfl, e3, (p 3).fderiv]
    fin_cases μ <;> simp

theorem uv_eq (GN m : ℝ) (hGN : 0 < GN) (hm : 0 < m) (x : Coord) (hr : 2 * GN * m < x 1) :
    kruskalU GN m (x 0) (x 1) ^ 2 - kruskalV GN m (x 0) (x 1) ^ 2
      = Real.exp (x 1 / (2 * GN * m)) * (x 1 / (2 * GN * m) - 1) := by
  have hc : 0 < 2 * GN * m := by positivity
  have hw : 0 < x 1 / (2 * GN * m) - 1 := by
    rw [sub_pos, one_lt_div hc]; exact hr
  have hs := Real.sq_sqrt hw.le
  have hch := Real.cosh_sq_sub_sinh_sq (x 0 / (4 * GN * m))
  have hE : Real.exp (x 1 / (4 * GN * m)) ^ 2 = Real.exp (x 1 / (2 * GN * m)) := by
    rw [sq, ← Real.exp_add]; congr 1; field_simp; ring
  simp only [kruskalU, kruskalV]
  linear_combination
    (√(x 1 / (2 * GN * m) - 1) ^ 2 * Real.exp (x 1 / (4 * GN * m)) ^ 2) * hch
    + Real.exp (x 1 / (4 * GN * m)) ^ 2 * hs + (x 1 / (2 * GN * m) - 1) * hE

theorem metric_eq (GN m : ℝ) (hGN : 0 < GN) (hm : 0 < m) (x : Coord) (hr : 2 * GN * m < x 1) :
    (jacobian (schwarzschildToKruskal GN m) x).transpose * kruskalMetricAt GN m (x 1) (x 2)
        * jacobian (schwarzschildToKruskal GN m) x = schwarzschild GN m x := by
  have hc : 0 < 2 * GN * m := by positivity
  have hw : 0 < x 1 / (2 * GN * m) - 1 := by
    rw [sub_pos, one_lt_div hc]; exact hr
  have hGN0 : GN ≠ 0 := hGN.ne'
  have hm0 : m ≠ 0 := hm.ne'
  have hSpos : 0 < √(x 1 / (2 * GN * m) - 1) := Real.sqrt_pos.mpr hw
  have hS2 : √(x 1 / (2 * GN * m) - 1) ^ 2 = x 1 / (2 * GN * m) - 1 := Real.sq_sqrt hw.le
  have hch := Real.cosh_sq_sub_sinh_sq (x 0 / (4 * GN * m))
  have hEE : Real.exp (x 1 / (4 * GN * m)) ^ 2 * Real.exp (-x 1 / (2 * GN * m)) = 1 := by
    rw [sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_zero]; congr 1; field_simp; ring
  rw [jac_eq GN m hGN hm x hr]
  simp only [kruskalMetricAt, schwarzschild, sphericalMetric]
  generalize √(x 1 / (2 * GN * m) - 1) = S at hSpos hS2 ⊢
  generalize Real.exp (x 1 / (4 * GN * m)) = E at hEE ⊢
  generalize Real.exp (-x 1 / (2 * GN * m)) = Ei at hEE ⊢
  generalize Real.cosh (x 0 / (4 * GN * m)) = C at hch ⊢
  generalize Real.sinh (x 0 / (4 * GN * m)) = Sh at hch ⊢
  have hrS : x 1 = 2 * GN * m * (S ^ 2 + 1) := by
    rw [hS2]; field_simp; ring
  generalize x 1 = r at hrS ⊢
  subst hrS
  have hS0 : S ≠ 0 := hSpos.ne'
  have hS1 : S ^ 2 + 1 ≠ 0 := by positivity
  have hR : (1 - 2 * GN * m / (2 * GN * m * (S ^ 2 + 1)))⁻¹ = (S ^ 2 + 1) / S ^ 2 := by
    have : 1 - 2 * GN * m / (2 * GN * m * (S ^ 2 + 1)) = S ^ 2 / (S ^ 2 + 1) := by
      field_simp; ring
    rw [this, inv_div]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply]
  · linear_combination (norm := skip)
      (-(32 * (GN * m) ^ 3 / (2 * GN * m * (S ^ 2 + 1)) * Ei) * (S * E / (4 * GN * m)) ^ 2) * hch
      + (-(32 * (GN * m) ^ 3 / (2 * GN * m * (S ^ 2 + 1))) * (S / (4 * GN * m)) ^ 2) * hEE
    field_simp
    ring
  · ring
  · ring
  · rw [hR]
    linear_combination (norm := skip)
      ((32 * (GN * m) ^ 3 / (2 * GN * m * (S ^ 2 + 1)) * Ei) * E ^ 2
        * (1 / (4 * GN * m * S) + S / (4 * GN * m)) ^ 2) * hch
      + ((32 * (GN * m) ^ 3 / (2 * GN * m * (S ^ 2 + 1)))
        * (1 / (4 * GN * m * S) + S / (4 * GN * m)) ^ 2) * hEE
    field_simp
    ring

end CGR879

open CarrollGR in open scoped ContDiff in
theorem solution (GN m : ℝ) (hGN : 0 < GN) (hm : 0 < m) (x : Coord)
    (hr : 2 * GN * m < x 1) :
    (jacobian (schwarzschildToKruskal GN m) x).transpose * kruskalMetricAt GN m (x 1) (x 2)
        * jacobian (schwarzschildToKruskal GN m) x = schwarzschild GN m x ∧
      kruskalU GN m (x 0) (x 1) ^ 2 - kruskalV GN m (x 0) (x 1) ^ 2
        = Real.exp (x 1 / (2 * GN * m)) * (x 1 / (2 * GN * m) - 1) := by
  exact ⟨CGR879.metric_eq GN m hGN hm x hr, CGR879.uv_eq GN m hGN hm x hr⟩
