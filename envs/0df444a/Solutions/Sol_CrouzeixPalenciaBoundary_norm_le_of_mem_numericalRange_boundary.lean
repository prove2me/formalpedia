-- Prove2me | solution 1 for CrouzeixPalenciaBoundary.norm_le_of_mem_numericalRange_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:45:51.938135+00:00
-- url     : https://prove2.me/submissions/797596e5-ee18-4051-be8b-71e0cef9bfbd

import Definitions.Def_Operator
import Definitions.Def_Operator_BoundaryCheck
import Theorems.Thm_norm_le_of_mem_numericalRange


set_option autoImplicit false
open Complex ContinuousLinearMap Metric Polynomial Set
open scoped ENNReal InnerProductSpace Interval Real
open CrouzeixPalenciaBoundary
universe u
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
namespace CrouzeixPalenciaBoundary
theorem _root_.solution (A : E →L[ℂ] E)
    {z : ℂ} (hz : z ∈ numericalRange A) : ‖z‖ ≤ ‖A‖ :=
  norm_le_of_mem_numericalRange A hz
end CrouzeixPalenciaBoundary
