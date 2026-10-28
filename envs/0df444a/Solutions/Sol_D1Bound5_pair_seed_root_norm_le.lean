-- Prove2me | solution 1 for D1Bound5.pair_seed_root_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:48:37.516801+00:00
-- url     : https://prove2.me/submissions/c14791d9-85d3-4f6d-8ae3-df405e0f4c4d

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Theorems.Thm_D1Bound5_QuadInt_norm_formula
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_quadInt_norm_add_le_twice

section
namespace D1Bound5
open QuadInt





/-- Every root needed for the radius-33 seed search has norm at most 132.
This deliberately loose bound keeps the finite search small and uniform. -/
theorem _root_.solution {tau nu : ℤ}
    (hd : 0 < discriminant tau nu) (a z q : QuadInt tau nu)
    (ha : a.norm ≤ 8) (hz : z.norm ≤ 1089) (hq : q*q = a*z+1) :
    q.norm ≤ 132 := by
  have hq0 := norm_nonneg hd q
  have hz0 := norm_nonneg hd z
  have hsum := quadInt_norm_add_le_twice hd (a*z) 1
  have hsq : q.norm*q.norm = (a*z+1).norm := by
    rw [← map_mul, hq]
  have hone : (1 : QuadInt tau nu).norm = 1 := by norm_num [norm_formula]
  rw [map_mul, hone] at hsum
  have hprod : a.norm*z.norm ≤ 8*1089 := mul_le_mul ha hz hz0 (by norm_num)
  nlinarith





























end D1Bound5
end
