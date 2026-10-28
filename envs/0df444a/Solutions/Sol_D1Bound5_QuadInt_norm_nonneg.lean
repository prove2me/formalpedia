-- Prove2me | solution 1 for D1Bound5.QuadInt.norm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:16:31.581798+00:00
-- url     : https://prove2.me/submissions/08b86d68-2700-4f02-a9ed-f7fafa143fd6

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Theorems.Thm_D1Bound5_QuadInt_four_norm

section
namespace D1Bound5



namespace QuadInt

variable {tau nu : ℤ}







theorem _root_.solution (hd : 0 < discriminant tau nu) (z : QuadInt tau nu) :
    0 ≤ z.norm := by
  have h := four_norm z
  have hprod := mul_nonneg hd.le (sq_nonneg z.im)
  nlinarith [sq_nonneg (2*z.re+tau*z.im)]









end QuadInt
end D1Bound5
end
