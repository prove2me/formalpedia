-- Prove2me | solution 1 for CrouzeixPalenciaBoundary.exists_smoothJordanDomain_norm_bound_crouzeixPolynomialAuxiliaryOperator_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:48:12.860256+00:00
-- url     : https://prove2.me/submissions/6b8a3275-f19b-4cd7-a497-ea19cd1f05bc

import Definitions.Def_Operator
import Definitions.Def_Operator_BoundaryCheck
import Theorems.Thm_exists_smoothJordanDomain_norm_bound_crouzeixPolynomialAuxiliaryOperator


set_option autoImplicit false
open Complex ContinuousLinearMap Metric Polynomial Set
open scoped ENNReal InnerProductSpace Interval Real
open CrouzeixPalenciaBoundary
universe u
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
namespace CrouzeixPalenciaBoundary
theorem _root_.solution
    [CompleteSpace E] (A : E →L[ℂ] E) (p : Polynomial ℂ) :
    ∃ (Omega : SmoothJordanDomain) (C : ℝ),
      closure (numericalRange A) ⊆ Omega.carrier ∧
        ‖crouzeixPolynomialAuxiliaryOperator A Omega p‖ ≤
          ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ * (2 * Real.pi * C) :=
  exists_smoothJordanDomain_norm_bound_crouzeixPolynomialAuxiliaryOperator A p
end CrouzeixPalenciaBoundary
