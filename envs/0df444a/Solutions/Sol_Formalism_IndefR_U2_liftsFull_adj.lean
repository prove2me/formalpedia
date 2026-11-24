-- Prove2me | solution 1 for Formalism.IndefR.U2.liftsFull_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:43:50.190816+00:00
-- url     : https://prove2.me/submissions/97ddc2ea-72b2-4ac6-b541-686e4bb92245

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_NormalDecomposition_DecompOfNormalStatement
import Theorems.Thm_Formalism_IndefR_U2_liftsFull_of
import Theorems.Thm_Formalism_IndefR_U2_isAdj_adjoint

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
theorem _root_.solution {θ : A →ₗ[ℂ] B} {op : I → Module.End ℂ A} {opB : I → Module.End ℂ B}
    {good : Submodule ℂ A} {goodB : Submodule ℂ B} {Ix : Set (I → ℂ)}
    (hD : OrthDecomp op good Ix) (hI : Intw θ op opB) (hG : GoodIn θ good goodB)
    (hO : OntoParts (LinearMap.adjoint θ) op opB good goodB Ix) : LiftsFull θ op opB good goodB Ix :=
  liftsFull_of hD hI hG (isAdj_adjoint θ) hO
end Formalism.IndefR.U2
