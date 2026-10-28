-- Prove2me | solution 1 for D1Bound5.product_neg_one_norms
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:20:39.979549+00:00
-- url     : https://prove2.me/submissions/fcff0235-29a4-4318-97c8-b36934aa101c

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg

section
namespace D1Bound5
open QuadInt



/-- Product minus one forces both positive integral norms to be one. -/
theorem _root_.solution {tau nu : ℤ}
    (hd : 0 < discriminant tau nu) (a b : QuadInt tau nu)
    (hprod : a*b+1=0) : a.norm=1 ∧ b.norm=1 := by
  have hp : a*b = -1 := eq_neg_iff_add_eq_zero.mpr hprod
  have hn : a.norm*b.norm=1 := by
    have hh := congrArg QuadraticAlgebra.norm hp
    simpa only [map_mul,QuadraticAlgebra.norm_neg,
      QuadraticAlgebra.norm_one] using hh
  have ha0 := QuadInt.norm_nonneg hd a
  have hb0 := QuadInt.norm_nonneg hd b
  have ha : 1 ≤ a.norm := by
    by_contra h
    have hz : a.norm=0 := by omega
    rw [hz] at hn
    norm_num at hn
  have hb : 1 ≤ b.norm := by
    by_contra h
    have hz : b.norm=0 := by omega
    rw [hz] at hn
    norm_num at hn
  have hm := mul_nonneg (show 0 ≤ a.norm-1 by omega) (show 0 ≤ b.norm-1 by omega)
  constructor <;> nlinarith only [hn,ha,hb,hm]













end D1Bound5
end
