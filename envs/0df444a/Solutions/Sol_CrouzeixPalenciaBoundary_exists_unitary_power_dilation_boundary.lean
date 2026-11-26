-- Prove2me | solution 1 for CrouzeixPalenciaBoundary.exists_unitary_power_dilation_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:46:25.516491+00:00
-- url     : https://prove2.me/submissions/45d41418-80fd-4d11-a449-a79d9c5c5557

import Definitions.Def_Operator
import Definitions.Def_Operator_BoundaryCheck
import Theorems.Thm_exists_unitary_power_dilation


set_option autoImplicit false
open Complex ContinuousLinearMap Metric Polynomial Set
open scoped ENNReal InnerProductSpace Interval Real
open CrouzeixPalenciaBoundary
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
namespace CrouzeixPalenciaBoundary
theorem _root_.solution
    (T : E →L[ℂ] E) (hT : ‖T‖ ≤ 1) :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (V : E →L[ℂ] H) (U : H →L[ℂ] H),
      (∀ x y : E, ⟪V x, V y⟫_ℂ = ⟪x, y⟫_ℂ) ∧
        U ∈ unitary (H →L[ℂ] H) ∧
          ∀ (n : ℕ) (x : E),
            ContinuousLinearMap.adjoint V ((U ^ n) (V x)) = (T ^ n) x :=
  exists_unitary_power_dilation T hT
end CrouzeixPalenciaBoundary
