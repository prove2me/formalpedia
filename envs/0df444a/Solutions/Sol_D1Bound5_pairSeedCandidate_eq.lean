-- Prove2me | solution 1 for D1Bound5.pairSeedCandidate_eq
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:38:59.648997+00:00
-- url     : https://prove2.me/submissions/b6a345d6-37e9-4f86-be63-91ffe8afb846

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
import Definitions.Def_D1Bound5_PairExtensionCore_Definitions
import Theorems.Thm_D1Bound5_QuadInt_norm_eq_zero_iff
import Theorems.Thm_D1Bound5_QuadInt_norm_formula

section
namespace D1Bound5
open QuadInt









/-- Every actual extension is reconstructed from either chosen square root. -/
theorem _root_.solution {tau nu : ℤ}
    (hd : 0 < discriminant tau nu) (a z q : QuadInt tau nu)
    (ha : a ≠ 0) (hq : q*q = a*z+1) : pairSeedCandidate a q = z := by
  have hn : a.norm ≠ 0 := fun h => ha ((norm_eq_zero_iff hd a).1 h)
  have hw : q*q-1 = a*z := by rw [hq]; ring
  have hre : (a.re+tau*a.im)*(a*z).re+nu*a.im*(a*z).im = a.norm*z.re := by
    simp only [norm_formula, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
    ring
  have him : a.re*(a*z).im-a.im*(a*z).re = a.norm*z.im := by
    simp only [norm_formula, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
    ring
  unfold pairSeedCandidate
  dsimp only
  rw [hw, hre, him]
  apply QuadraticAlgebra.ext <;> simp only [Int.mul_ediv_cancel_left _ hn]

























end D1Bound5
end
