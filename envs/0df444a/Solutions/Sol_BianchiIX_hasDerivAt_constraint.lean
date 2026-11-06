-- Prove2me | solution 1 for BianchiIX.hasDerivAt_constraint
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T13:03:05.728199+00:00
-- url     : https://prove2.me/submissions/f0395337-2270-439a-b4b6-f16ae92e3aad

import Definitions.Def_BianchiIX_Algebra_Flow
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open BianchiIX
noncomputable section


/-- This is an actual derivative along a solution, not only a polynomial identity. -/
theorem solution
    {p s a b c : ℝ → ℝ} {t : ℝ}
    (hp : HasDerivAt p (shearPlus (p t) (a t) (b t) (c t)) t)
    (hs : HasDerivAt s (shearMinus (s t) (a t) (b t) (c t)) t)
    (ha : HasDerivAt a (rateOne (p t) (s t) * a t) t)
    (hb : HasDerivAt b (rateTwo (p t) (s t) * b t) t)
    (hc : HasDerivAt c (rateThree (p t) (s t) * c t) t) :
    HasDerivAt (fun u => constraint (p u) (s u) (a u) (b u) (c u)) 0 t := by
  convert ((hp.pow 2).add (hs.pow 2)).add
    (((ha.pow 2).add (hb.pow 2)).add (hc.pow 2) |>.sub
      ((((ha.mul hb).add (hb.mul hc)).add (hc.mul ha)).const_mul 2)) using 1 <;>
    first | rfl | (norm_num [constraint, shearSq, curvature, shearPlus, shearMinus,
      rateOne, rateTwo, rateThree]; ring)
