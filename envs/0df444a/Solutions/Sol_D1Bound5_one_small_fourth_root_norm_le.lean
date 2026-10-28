-- Prove2me | solution 1 for D1Bound5.one_small_fourth_root_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:22:21.149774+00:00
-- url     : https://prove2.me/submissions/c56ecbac-fe47-4fe4-83fc-c6ff7c95a174

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
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_quadInt_norm_add_le_twice

section
namespace D1Bound5
open QuadInt



/-- A uniform root bound for all 56 fourth-entry certificates. -/
theorem _root_.solution {tau nu : ℤ}
    (hd : 0 < discriminant tau nu) (a z q : QuadInt tau nu)
    (ha : a.norm ≤ 2) (hz : z.norm ≤ 21270) (hq : q*q = a*z+1) :
    q.norm ≤ 300 := by
  have hz0 := norm_nonneg hd z
  have hsum := quadInt_norm_add_le_twice hd (a*z) 1
  have hsq : q.norm*q.norm = (a*z+1).norm := by rw [← map_mul, hq]
  have hone : (1 : QuadInt tau nu).norm = 1 := by norm_num [norm_formula]
  rw [map_mul, hone] at hsum
  have hprod : a.norm*z.norm ≤ 2*21270 := mul_le_mul ha hz hz0 (by norm_num)
  by_contra h
  have h301 : 301 ≤ q.norm := by omega
  nlinarith



















end D1Bound5
end
