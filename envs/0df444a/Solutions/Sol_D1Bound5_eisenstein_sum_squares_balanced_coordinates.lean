-- Prove2me | solution 1 for D1Bound5.eisenstein_sum_squares_balanced_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:23:58.888989+00:00
-- url     : https://prove2.me/submissions/17e1e774-bfe1-40db-b559-309574c76c3f

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_EisensteinPellDescent_Definitions

section
namespace D1Bound5
open QuadInt



private theorem eisensteinCoordinateNorm_nonneg (x y : ℤ) :
    0 ≤ eisensteinCoordinateNorm x y := by
  dsimp [eisensteinCoordinateNorm]
  nlinarith only [sq_nonneg (2*x+y), sq_nonneg y]

private theorem eisensteinCoordinateNorm_small (x y : ℤ)
    (h : eisensteinCoordinateNorm x y ≤ 2) :
    -1 ≤ x ∧ x ≤ 1 ∧ -1 ≤ y ∧ y ≤ 1 := by
  dsimp [eisensteinCoordinateNorm] at h
  have hx : 3*x^2 ≤ 8 := by nlinarith only [h, sq_nonneg (x+2*y)]
  have hy : 3*y^2 ≤ 8 := by nlinarith only [h, sq_nonneg (2*x+y)]
  have hxl : -1 ≤ x := by
    by_contra hn
    have hn' : x ≤ -2 := by omega
    nlinarith only [hx, hn', sq_nonneg (x+2)]
  have hxu : x ≤ 1 := by
    by_contra hn
    have hn' : 2 ≤ x := by omega
    nlinarith only [hx, hn', sq_nonneg (x-2)]
  have hyl : -1 ≤ y := by
    by_contra hn
    have hn' : y ≤ -2 := by omega
    nlinarith only [hy, hn', sq_nonneg (y+2)]
  have hyu : y ≤ 1 := by
    by_contra hn
    have hn' : 2 ≤ y := by omega
    nlinarith only [hy, hn', sq_nonneg (y-2)]
  exact ⟨hxl,hxu,hyl,hyu⟩

private theorem eisenstein_pell_seed (x y u v : ℤ)
    (hR : x^2-y^2+u^2-v^2 = 0)
    (hI : 2*x*y+y^2+2*u*v+v^2 = 1)
    (hM : eisensteinCoordinateNorm x y+eisensteinCoordinateNorm u v ≤ 2) :
    (u = y ∧ v = x) ∨ (u = -y ∧ v = -x) := by
  have hxy := eisensteinCoordinateNorm_small x y
    (by linarith only [hM, eisensteinCoordinateNorm_nonneg u v])
  have huv := eisensteinCoordinateNorm_small u v
    (by linarith only [hM, eisensteinCoordinateNorm_nonneg x y])
  obtain ⟨hxl,hxu,hyl,hyu⟩ := hxy
  obtain ⟨hul,huu,hvl,hvu⟩ := huv
  interval_cases x <;> interval_cases y <;> interval_cases u <;> interval_cases v <;>
    norm_num at hR <;> norm_num at hI <;> norm_num

private theorem eisenstein_pell_decrease (M D : ℤ)
    (hM : 2 < M) (hD : 0 ≤ D) (hP : M^2-3*D^2 = 1) :
    7*M-12*D < M := by
  have hM3 : 3 ≤ M := by omega
  have hsq : M^2 < 4*D^2 := by
    nlinarith only [hP, hM3, sq_nonneg (M-3)]
  have hMD : M < 2*D := by
    by_contra hn
    have hle : 2*D ≤ M := le_of_not_gt hn
    have hplus : 0 ≤ M+2*D := by omega
    nlinarith only [hsq, mul_nonneg (sub_nonneg.mpr hle) hplus]
  omega

/-- All Eisenstein integral solutions of r²+q²=ω are balanced. The proof
uses the exact Pell invariant M²-3D²=1 and descent by the integral matrix
with entries 2 and ±sqrt(-3), down to 81 checked coordinate cases. -/
theorem _root_.solution (x y u v : ℤ)
    (hR : x^2-y^2+u^2-v^2 = 0)
    (hI : 2*x*y+y^2+2*u*v+v^2 = 1) :
    (u = y ∧ v = x) ∨ (u = -y ∧ v = -x) := by
  suffices hmain : ∀ n : ℕ, ∀ x y u v : ℤ,
      (eisensteinCoordinateNorm x y+eisensteinCoordinateNorm u v).toNat = n →
      x^2-y^2+u^2-v^2 = 0 → 2*x*y+y^2+2*u*v+v^2 = 1 →
      (u = y ∧ v = x) ∨ (u = -y ∧ v = -x) by
    exact hmain _ x y u v rfl hR hI
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x y u v hn hR hI
    let M := eisensteinCoordinateNorm x y+eisensteinCoordinateNorm u v
    let D := x*v-y*u
    have hM0 : 0 ≤ M := add_nonneg
      (eisensteinCoordinateNorm_nonneg x y) (eisensteinCoordinateNorm_nonneg u v)
    have hP : M^2-3*D^2 = 1 := by
      have hid : M^2-3*D^2 =
          (x^2-y^2+u^2-v^2)^2+
          (x^2-y^2+u^2-v^2)*(2*x*y+y^2+2*u*v+v^2)+
          (2*x*y+y^2+2*u*v+v^2)^2 := by
        dsimp [M, D, eisensteinCoordinateNorm]
        ring
      rw [hR, hI] at hid
      norm_num at hid
      exact hid
    by_cases hsmall : M ≤ 2
    · exact eisenstein_pell_seed x y u v hR hI hsmall
    have hMlarge : 2 < M := lt_of_not_ge hsmall
    by_cases hD : 0 ≤ D
    · let X := 2*x-u-2*v
      let Y := 2*y+2*u+v
      let U := 2*u+x+2*y
      let V := 2*v-2*x-y
      have hR' : X^2-Y^2+U^2-V^2 = 0 := by
        dsimp [X, Y, U, V]
        linear_combination hR
      have hI' : 2*X*Y+Y^2+2*U*V+V^2 = 1 := by
        dsimp [X, Y, U, V]
        linear_combination hI
      have hnorm : eisensteinCoordinateNorm X Y+eisensteinCoordinateNorm U V =
          7*M-12*D := by
        dsimp [X, Y, U, V, M, D, eisensteinCoordinateNorm]
        ring
      have hN0 : 0 ≤ eisensteinCoordinateNorm X Y+eisensteinCoordinateNorm U V :=
        add_nonneg (eisensteinCoordinateNorm_nonneg X Y) (eisensteinCoordinateNorm_nonneg U V)
      have hlt : (eisensteinCoordinateNorm X Y+eisensteinCoordinateNorm U V).toNat < n := by
        have hd := eisenstein_pell_decrease M D hMlarge hD hP
        change M.toNat = n at hn
        omega
      have hb := ih _ hlt X Y U V rfl hR' hI'
      dsimp [X, Y, U, V] at hb
      rcases hb with ⟨h1,h2⟩ | ⟨h1,h2⟩
      · exact Or.inl ⟨by omega, by omega⟩
      · exact Or.inr ⟨by omega, by omega⟩
    · let X := 2*x+u+2*v
      let Y := 2*y-2*u-v
      let U := 2*u-x-2*y
      let V := 2*v+2*x+y
      have hR' : X^2-Y^2+U^2-V^2 = 0 := by
        dsimp [X, Y, U, V]
        linear_combination hR
      have hI' : 2*X*Y+Y^2+2*U*V+V^2 = 1 := by
        dsimp [X, Y, U, V]
        linear_combination hI
      have hnorm : eisensteinCoordinateNorm X Y+eisensteinCoordinateNorm U V =
          7*M+12*D := by
        dsimp [X, Y, U, V, M, D, eisensteinCoordinateNorm]
        ring
      have hN0 : 0 ≤ eisensteinCoordinateNorm X Y+eisensteinCoordinateNorm U V :=
        add_nonneg (eisensteinCoordinateNorm_nonneg X Y) (eisensteinCoordinateNorm_nonneg U V)
      have hlt : (eisensteinCoordinateNorm X Y+eisensteinCoordinateNorm U V).toNat < n := by
        have hd := eisenstein_pell_decrease M (-D) hMlarge (by omega)
          (by simpa only [neg_sq] using hP)
        change M.toNat = n at hn
        omega
      have hb := ih _ hlt X Y U V rfl hR' hI'
      dsimp [X, Y, U, V] at hb
      rcases hb with ⟨h1,h2⟩ | ⟨h1,h2⟩
      · exact Or.inl ⟨by omega, by omega⟩
      · exact Or.inr ⟨by omega, by omega⟩

end D1Bound5
end
