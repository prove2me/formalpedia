-- Prove2me | solution 1 for D1Bound5.quadInt_norm_add_le_twice
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:48:38.565295+00:00
-- url     : https://prove2.me/submissions/f7452082-10fd-440e-940b-0b87d05f459b

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

section
namespace D1Bound5
open QuadInt



/-- The norm parallelogram identity gives a division-free root bound. -/
theorem _root_.solution {tau nu : ℤ}
    (hd : 0 < discriminant tau nu) (x y : QuadInt tau nu) :
    (x+y).norm ≤ 2*x.norm+2*y.norm := by
  have hn := norm_nonneg hd (x-y)
  have hi : (x+y).norm+(x-y).norm = 2*x.norm+2*y.norm := by
    simp only [norm_formula, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add,
      QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub]
    ring
  omega































end D1Bound5
end
