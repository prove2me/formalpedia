-- Prove2me | solution 1 for CrouzeixPalenciaBoundary.convex_numericalRange_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:46:09.279336+00:00
-- url     : https://prove2.me/submissions/65ef8193-5e23-4503-8711-b79e072406f5

import Definitions.Def_Operator
import Definitions.Def_Operator_BoundaryCheck
import Theorems.Thm_convex_numericalRange


set_option autoImplicit false
open Complex ContinuousLinearMap Metric Polynomial Set
open scoped ENNReal InnerProductSpace Interval Real
open CrouzeixPalenciaBoundary
universe u
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
namespace CrouzeixPalenciaBoundary
theorem _root_.solution (A : E →L[ℂ] E) :
    Convex ℝ (numericalRange A) :=
  convex_numericalRange A
end CrouzeixPalenciaBoundary
