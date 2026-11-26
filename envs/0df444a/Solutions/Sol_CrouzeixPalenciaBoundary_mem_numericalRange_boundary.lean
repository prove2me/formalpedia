-- Prove2me | solution 1 for CrouzeixPalenciaBoundary.mem_numericalRange_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:45:51.009867+00:00
-- url     : https://prove2.me/submissions/51dbe331-f04b-4648-94d2-327a98ed6e21

import Definitions.Def_Operator
import Definitions.Def_Operator_BoundaryCheck
import Theorems.Thm_mem_numericalRange
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex ContinuousLinearMap Metric Polynomial Set
open scoped ENNReal InnerProductSpace Interval Real
open CrouzeixPalenciaBoundary
universe u
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
namespace CrouzeixPalenciaBoundary
theorem _root_.solution (A : E →L[ℂ] E) (z : ℂ) :
    z ∈ numericalRange A ↔ ∃ x : E, ‖x‖ = 1 ∧ ⟪x, A x⟫_ℂ = z :=
  mem_numericalRange A z
end CrouzeixPalenciaBoundary
