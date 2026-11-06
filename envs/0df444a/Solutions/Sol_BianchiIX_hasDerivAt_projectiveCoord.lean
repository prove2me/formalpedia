-- Prove2me | solution 1 for BianchiIX.hasDerivAt_projectiveCoord
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:13:14.392532+00:00
-- url     : https://prove2.me/submissions/e22fd70f-3b90-4ecd-b937-51ec5a396782

import Definitions.Def_BianchiIX_Algebra_Coordinates
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

open BianchiIX
noncomputable section


/-- Quotient differentiation with the original time variable. -/
theorem solution
    {p z : ℝ → ℝ} {p' z' t : ℝ}
    (hp : HasDerivAt p p' t) (hz : HasDerivAt z z' t) (hA : 1 + p t ≠ 0) :
    HasDerivAt (fun x => projectiveCoord (p x) (z x))
      (Real.sqrt 3 * (z' * (1 + p t) - z t * p') / (1 + p t) ^ 2) t := by
  convert (hz.const_mul (Real.sqrt 3)).div (hp.const_add 1) hA using 1 <;>
    first | rfl | ring
