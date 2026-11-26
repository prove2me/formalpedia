-- Prove2me | solution 1 for CrouzeixPalenciaBoundary.contourIntegral_eq_zero_of_hasDerivAt_of_closed_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:47:45.09687+00:00
-- url     : https://prove2.me/submissions/6e006c18-c394-440f-a322-873547fefd99

import Definitions.Def_Operator
import Definitions.Def_Operator_BoundaryCheck
import Theorems.Thm_contourIntegral_eq_zero_of_hasDerivAt_of_closed


set_option autoImplicit false
open Complex ContinuousLinearMap Metric Polynomial Set
open scoped ENNReal InnerProductSpace Interval Real
open CrouzeixPalenciaBoundary
universe u
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
namespace CrouzeixPalenciaBoundary
theorem _root_.solution
    {f Fp : ℂ → F} {γ : ℝ → ℂ}
    (hγ : ∀ t ∈ Icc (0 : ℝ) (2 * π), DifferentiableAt ℝ γ t)
    (hF : ∀ t ∈ Icc (0 : ℝ) (2 * π), HasDerivAt Fp (f (γ t)) (γ t))
    (hint : ContourIntegrable f γ) (hclosed : γ (2 * π) = γ 0) :
    contourIntegral f γ = 0 :=
  contourIntegral_eq_zero_of_hasDerivAt_of_closed hγ hF hint hclosed
end CrouzeixPalenciaBoundary
