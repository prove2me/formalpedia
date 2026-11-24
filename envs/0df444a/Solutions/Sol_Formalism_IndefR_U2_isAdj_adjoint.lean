-- Prove2me | solution 1 for Formalism.IndefR.U2.isAdj_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:13:43.154192+00:00
-- url     : https://prove2.me/submissions/f21269a3-756c-492c-9818-2a4ded97544d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_NormalDecomposition_DecompOfNormalStatement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.U2
variable {I : Type*} {A B : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℂ A] [NormedAddCommGroup B] [InnerProductSpace ℂ B]
variable {θ : A →ₗ[ℂ] B} {θa : B →ₗ[ℂ] A} {op : I → Module.End ℂ A} {opB : I → Module.End ℂ B}
  {good : Submodule ℂ A} {goodB : Submodule ℂ B} {Ix : Set (I → ℂ)}
variable [FiniteDimensional ℂ A] [FiniteDimensional ℂ B]
namespace Formalism.IndefR.U2
theorem _root_.solution (θ : A →ₗ[ℂ] B) : IsAdj θ (LinearMap.adjoint θ) :=
  fun x y => (LinearMap.adjoint_inner_right θ x y).symm
end Formalism.IndefR.U2
