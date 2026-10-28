-- Prove2me | solution 1 for D1Bound5.first_pair_root_norm_le_eight
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:55:39.900371+00:00
-- url     : https://prove2.me/submissions/39dd74fe-ccc1-4ffe-af3b-423bc589d2df

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
import Theorems.Thm_D1Bound5_QuadInt_norm_formula

section
namespace D1Bound5
open QuadInt

/-- A root of a first-pair product needs only the norm-eight disk. -/
theorem _root_.solution {tau nu : ℤ}
    (hd : 0 < discriminant tau nu) (a b q : QuadInt tau nu)
    (hab : a.norm*b.norm ≤ 63) (hq : q*q = a*b+1) : q.norm ≤ 8 := by
  let z := a*b
  let v : ℤ := 2*z.re+tau*z.im
  have hv : v^2 ≤ 4*z.norm := by
    have hdisc := mul_nonneg (le_of_lt hd) (sq_nonneg z.im)
    have hfour : 4*z.norm = v^2+discriminant tau nu*z.im^2 := by
      simp only [norm_formula, discriminant]
      dsimp [v]
      ring
    nlinarith only [hfour, hdisc]
  have hz : z.norm ≤ 63 := by simpa only [z, map_mul] using hab
  have hv15 : v ≤ 15 := by
    by_contra h
    have hv16 : 16 ≤ v := by omega
    nlinarith
  have hid : (z+1).norm = z.norm+v+1 := by
    simp only [norm_formula, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add,
      QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
    dsimp [v]
    ring
  have hsq : q.norm*q.norm = (z+1).norm := by rw [← map_mul, hq]
  by_contra h
  have hq9 : 9 ≤ q.norm := by omega
  nlinarith





















end D1Bound5
end
