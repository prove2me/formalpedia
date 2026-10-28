-- Prove2me | solution 1 for D1Bound5.small_tail_discriminant_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:21:48.471442+00:00
-- url     : https://prove2.me/submissions/8561d849-cb02-44e5-b93e-25e4b994d368

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
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Theorems.Thm_D1Bound5_QuadInt_discriminant_le_four_bound
import Theorems.Thm_D1Bound5_QuadInt_norm_formula
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg

section
namespace D1Bound5

open QuadInt










/-- Integer real coordinates of squared size from nine through fifteen
are precisely plus or minus three. -/
theorem integer_square_nine_fifteen (n : ℤ) (hlo : 9 ≤ n^2) (hhi : n^2 ≤ 15) :
    n = 3 ∨ n = -3 := by
  have h1 : n < 4 := by nlinarith [sq_nonneg (n-4)]
  have h2 : -4 < n := by nlinarith [sq_nonneg (n+4)]
  have h3 : -3 ≤ n := by omega
  have h4 : n ≤ 3 := by omega
  interval_cases n <;> norm_num at *

/-- The small-tail search reduces to Delta<=60 even when both entries
are real. In that case their nonreal square root supplies the cutoff. -/
theorem _root_.solution {tau nu : ℤ}
    (hd : 0 < QuadInt.discriminant tau nu) (b c r : QuadInt tau nu)
    (hbc : b ≠ c) (hNb : 9 ≤ b.norm) (hNbc : b.norm ≤ c.norm)
    (hNc : c.norm ≤ 15) (hr : r*r = b*c+1) : QuadInt.discriminant tau nu ≤ 60 := by
  by_contra hdelta
  have hbim : b.im = 0 := by
    by_contra h
    have := QuadInt.discriminant_le_four_bound hd (hNbc.trans hNc) h
    omega
  have hcim : c.im = 0 := by
    by_contra h
    have := QuadInt.discriminant_le_four_bound hd hNc h
    omega
  have hbN : b.norm = b.re^2 := by simp [QuadInt.norm_formula, hbim]
  have hcN : c.norm = c.re^2 := by simp [QuadInt.norm_formula, hcim]
  have hbchoices := integer_square_nine_fifteen b.re (by omega) (by omega)
  have hcchoices := integer_square_nine_fifteen c.re (by omega) (by omega)
  have hneq : b.re ≠ c.re := by
    intro h
    exact hbc (QuadraticAlgebra.ext h (hbim.trans hcim.symm))
  have hp : b.re*c.re+1 = -8 := by
    rcases hbchoices with h | h <;> rcases hcchoices with h' | h' <;> simp_all
  have hprod : b*c+1 = (⟨-8,0⟩ : QuadInt tau nu) := by
    ext <;> simp [hbim, hcim, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, hp]
  rw [hprod] at hr
  have hn := congrArg (QuadraticAlgebra.norm : QuadInt tau nu → ℤ) hr
  rw [map_mul] at hn
  have hn2 : r.norm*r.norm = 64 := by simpa [QuadInt.norm_formula] using hn
  have hnr : r.norm = 8 := by
    have hnonneg := QuadInt.norm_nonneg hd r
    nlinarith
  have hrim : r.im = 0 := by
    by_contra h
    have hh := QuadInt.discriminant_le_four_bound hd (le_of_eq hnr) h
    omega
  have hrre := congrArg (fun z : QuadInt tau nu => z.re) hr
  simp [hrim] at hrre
  nlinarith [sq_nonneg r.re]

end D1Bound5
end
