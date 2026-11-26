-- Prove2me | solution 1 for CrouzeixPalenciaBoundary.vonNeumann_inequality_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:46:30.375438+00:00
-- url     : https://prove2.me/submissions/bb7a348b-71b3-4be8-86f7-9666e6c15da7

import Definitions.Def_Operator
import Definitions.Def_Operator_BoundaryCheck
import Theorems.Thm_vonNeumann_inequality


set_option autoImplicit false
open Complex ContinuousLinearMap Metric Polynomial Set
open scoped ENNReal InnerProductSpace Interval Real
open CrouzeixPalenciaBoundary
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
namespace CrouzeixPalenciaBoundary
theorem _root_.solution
    (T : E →L[ℂ] E) (hT : ‖T‖ ≤ 1) (p : ℂ[X]) :
    ‖aeval T p‖ ≤ polynomialSupNorm p (Metric.closedBall (0 : ℂ) 1) :=
  vonNeumann_inequality T hT p
end CrouzeixPalenciaBoundary
