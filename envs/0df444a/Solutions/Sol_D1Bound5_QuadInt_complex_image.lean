-- Prove2me | solution 1 for D1Bound5.QuadInt.complex_image
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:33:36.182546+00:00
-- url     : https://prove2.me/submissions/fdbba51e-044c-4802-8957-4a4bebca2588

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
namespace D1Bound5.QuadInt

open scoped QuadraticAlgebra

variable {tau nu : ℤ}

/-- The image of an arbitrary coordinate element under a complex ring map. -/
theorem _root_.solution (f : QuadInt tau nu →+* ℂ) (z : QuadInt tau nu) :
    f z = (z.re : ℂ)+(z.im : ℂ)*f QuadraticAlgebra.omega := by
  have hz : z = (z.re : QuadInt tau nu) + (z.im : QuadInt tau nu)*QuadraticAlgebra.omega := by
    ext <;> simp [QuadraticAlgebra.omega]
  calc
    f z = f ((z.re : QuadInt tau nu) + (z.im : QuadInt tau nu)*QuadraticAlgebra.omega) := congrArg f hz
    _ = _ := by simp only [map_add, map_mul, map_intCast]









end D1Bound5.QuadInt
end
