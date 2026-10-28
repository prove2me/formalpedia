-- Prove2me | solution 1 for D1Bound5.one_three_integer_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:29:08.26589+00:00
-- url     : https://prove2.me/submissions/48a9bb75-3363-4218-8b64-0dad28649d5e

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

section
namespace D1Bound5




/-- The integral conic obstruction in lem:pr-one-three. Positivity of both
factors already forces k nonzero; no separate irrationality argument is needed. -/
theorem _root_.solution (delta e f g h k : ℤ)
    (hd : 3 ≤ delta) (hf : f ≠ 0) (hg : g ≠ 0)
    (him : g*h = 3*e*f)
    (hre : 3*e^2-g^2+delta*(h^2-3*f^2) = 8)
    (hk : e*h-f*g = 2*k) : False := by
  let X := 3*e^2-g^2
  let V := h^2-3*f^2
  have hsum : X+delta*V = 8 := hre
  have hg2 : 0 < g^2 := sq_pos_of_ne_zero hg
  have hf2 : 0 < f^2 := sq_pos_of_ne_zero hf
  have hrel : g^2*V = 3*f^2*X := by
    dsimp [X, V]
    linear_combination (g*h+3*e*f)*him
  have hprod : X*V = 12*k^2 := by
    calc
      _ = 3*(e*h-f*g)^2-(g*h-3*e*f)^2 := by dsimp [X,V]; ring
      _ = 12*k^2 := by rw [him, hk]; ring
  have hX : 0 < X := by
    by_contra hX
    have hXle : X ≤ 0 := le_of_not_gt hX
    have hR : 3*f^2*X ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by norm_num) hf2.le) hXle
    have hVle : V ≤ 0 := by
      by_contra hV
      have hp : 0 < g^2*V := mul_pos hg2 (lt_of_not_ge hV)
      linarith [hrel]
    have hDV : delta*V ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by omega) hVle
    linarith [hsum]
  have hV : 0 < V := by
    by_contra hV
    have hp : g^2*V ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hg2.le (le_of_not_gt hV)
    have hq : 0 < 3*f^2*X := mul_pos (mul_pos (by norm_num) hf2) hX
    linarith [hrel]
  have hXV : 0 < X*V := mul_pos hX hV
  have hk1 : 1 ≤ k^2 := by omega
  have hdk : 3 ≤ delta*k^2 := by
    have hp := mul_le_mul_of_nonneg_right hd (sq_nonneg k)
    linarith
  have hid : (X+delta*V)^2-(X-delta*V)^2 = 4*delta*(X*V) := by ring
  rw [hsum, hprod] at hid
  nlinarith [sq_nonneg (X-delta*V)]





end D1Bound5
end
