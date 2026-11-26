-- Prove2me | solution 1 for CrouzeixPalenciaBoundary.convexThickeningApprox_spec_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:48:03.711662+00:00
-- url     : https://prove2.me/submissions/bd9cc066-f2ae-427d-9f53-4e831b8be4da

import Definitions.Def_Operator
import Definitions.Def_Operator_BoundaryCheck
import Theorems.Thm_convexThickeningApprox_spec


set_option autoImplicit false
open Complex ContinuousLinearMap Metric Polynomial Set
open scoped ENNReal InnerProductSpace Interval Real
open CrouzeixPalenciaBoundary
universe u
namespace CrouzeixPalenciaBoundary
theorem _root_.solution
    (K : Set ℂ) (hcompact : IsCompact K) (hconvex : Convex ℝ K) :
    (∀ n, K ⊆ convexThickeningApprox K n ∧
      IsOpen (convexThickeningApprox K n) ∧
      StrictConvex ℝ (convexThickeningApprox K n)) ∧
      (⋂ n, convexThickeningApprox K n) = K :=
  convexThickeningApprox_spec K hcompact hconvex
end CrouzeixPalenciaBoundary
