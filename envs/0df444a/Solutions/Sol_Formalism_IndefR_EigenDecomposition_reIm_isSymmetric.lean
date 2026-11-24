-- Prove2me | solution 1 for Formalism.IndefR.EigenDecomposition.reIm_isSymmetric
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:03:39.377141+00:00
-- url     : https://prove2.me/submissions/bbea834d-55bc-44f6-87ae-a778ac00b792

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_EigenDecomposition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Formalism Formalism.IndefR Formalism.IndefR.EigenDecomposition
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
namespace Formalism.IndefR.EigenDecomposition
theorem _root_.solution (T : H →ₗ[ℂ] H) (b : Bool) : (reIm T b).IsSymmetric := by
  intro x y
  cases b <;>
    simp [reIm, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, inner_add_left,
      inner_add_right, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_right] <;> ring
end Formalism.IndefR.EigenDecomposition
