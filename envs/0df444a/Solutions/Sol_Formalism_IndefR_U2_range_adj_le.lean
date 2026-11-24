-- Prove2me | solution 1 for Formalism.IndefR.U2.range_adj_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:34:28.971431+00:00
-- url     : https://prove2.me/submissions/424f42c9-4a9b-4019-a47a-6aa7129a0c40

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
namespace Formalism.IndefR.U2
theorem _root_.solution (hA : IsAdj θ θa) : LinearMap.range θa ≤ (LinearMap.ker θ)ᗮ := by
  rintro _ ⟨y, rfl⟩
  rw [Submodule.mem_orthogonal]
  intro u hu
  rw [← hA, LinearMap.mem_ker.mp hu, inner_zero_left]
end Formalism.IndefR.U2
