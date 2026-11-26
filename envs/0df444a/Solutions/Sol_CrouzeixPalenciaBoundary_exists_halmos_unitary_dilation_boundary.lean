-- Prove2me | solution 1 for CrouzeixPalenciaBoundary.exists_halmos_unitary_dilation_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:46:24.622341+00:00
-- url     : https://prove2.me/submissions/a602aa64-c912-41d2-8ef7-a7be650f0be7

import Definitions.Def_Operator
import Definitions.Def_Operator_BoundaryCheck
import Theorems.Thm_exists_halmos_unitary_dilation


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
    ∃ U : WithLp 2 (E × E) →L[ℂ] WithLp 2 (E × E),
      U ∈ unitary (WithLp 2 (E × E) →L[ℂ] WithLp 2 (E × E)) ∧
        ∀ x : E, (U (WithLp.toLp 2 (x, 0))).fst = T x :=
  exists_halmos_unitary_dilation T hT
end CrouzeixPalenciaBoundary
