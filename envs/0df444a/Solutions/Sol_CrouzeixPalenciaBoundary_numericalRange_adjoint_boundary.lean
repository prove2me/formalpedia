-- Prove2me | solution 1 for CrouzeixPalenciaBoundary.numericalRange_adjoint_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:46:18.834704+00:00
-- url     : https://prove2.me/submissions/a81a9359-6153-40df-8d05-2c5f4a1ed7ef

import Definitions.Def_Operator
import Definitions.Def_Operator_BoundaryCheck
import Theorems.Thm_numericalRange_adjoint


set_option autoImplicit false
open Complex ContinuousLinearMap Metric Polynomial Set
open scoped ENNReal InnerProductSpace Interval Real
open CrouzeixPalenciaBoundary
universe u
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
namespace CrouzeixPalenciaBoundary
theorem _root_.solution (A : E →L[ℂ] E) :
    numericalRange (ContinuousLinearMap.adjoint A) =
      (starRingEnd ℂ) '' numericalRange A :=
  numericalRange_adjoint A
end CrouzeixPalenciaBoundary
