-- Prove2me | solution 1 for BianchiIX.hasDerivAt_wall_product
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T13:04:05.495643+00:00
-- url     : https://prove2.me/submissions/f552fe64-fb8b-4c67-85ac-78b34e20cbd7

import Definitions.Def_BianchiIX_Algebra_Flow
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open BianchiIX
noncomputable section


theorem solution
    {p s a b c : ℝ → ℝ} {t : ℝ}
    (ha : HasDerivAt a (rateOne (p t) (s t) * a t) t)
    (hb : HasDerivAt b (rateTwo (p t) (s t) * b t) t)
    (hc : HasDerivAt c (rateThree (p t) (s t) * c t) t) :
    HasDerivAt (fun u => a u * b u * c u)
      (-3 * shearSq (p t) (s t) * (a t * b t * c t)) t := by
  convert (ha.mul hb).mul hc using 1 <;>
    first | rfl | (simp only [rateOne, rateTwo, rateThree, Pi.mul_apply]; ring)
