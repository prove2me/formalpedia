-- Prove2me | solution 1 for CrouzeixPalenciaBoundary.crouzeix_palencia_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:46:21.296937+00:00
-- url     : https://prove2.me/submissions/023fdbbd-bc6a-4709-8cf3-a6edd4b870c5

import Definitions.Def_Operator
import Definitions.Def_Operator_BoundaryCheck
import Theorems.Thm_crouzeix_palencia


set_option autoImplicit false
open Complex ContinuousLinearMap Metric Polynomial Set
open scoped ENNReal InnerProductSpace Interval Real
open CrouzeixPalenciaBoundary
universe u
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
namespace CrouzeixPalenciaBoundary
theorem _root_.solution (A : E →L[ℂ] E) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) :=
  crouzeix_palencia A
end CrouzeixPalenciaBoundary
