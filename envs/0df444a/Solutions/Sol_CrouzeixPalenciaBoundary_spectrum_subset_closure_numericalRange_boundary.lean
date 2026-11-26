-- Prove2me | solution 1 for CrouzeixPalenciaBoundary.spectrum_subset_closure_numericalRange_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:46:12.952797+00:00
-- url     : https://prove2.me/submissions/f907bc8e-6c99-4947-ada4-78c68af7d5ee

import Definitions.Def_Operator
import Definitions.Def_Operator_BoundaryCheck
import Theorems.Thm_spectrum_subset_closure_numericalRange


set_option autoImplicit false
open Complex ContinuousLinearMap Metric Polynomial Set
open scoped ENNReal InnerProductSpace Interval Real
open CrouzeixPalenciaBoundary
universe u
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
namespace CrouzeixPalenciaBoundary
theorem _root_.solution (A : E →L[ℂ] E) :
    spectrum ℂ (A : E →L[ℂ] E) ⊆ closure (numericalRange A) :=
  spectrum_subset_closure_numericalRange A
end CrouzeixPalenciaBoundary
