-- Prove2me | solution 1 for Formalism.IndefR.U2.map_eigPart
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:58:31.861808+00:00
-- url     : https://prove2.me/submissions/a8d49214-080e-49fa-b65c-705d1b14dccd

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_NormalDecomposition_DecompOfNormalStatement
import Theorems.Thm_Formalism_IndefR_U2_mem_eigPart

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
theorem _root_.solution (hI : Intw θ op opB) {c : I → ℂ} {x : A} (hx : x ∈ eigPart op c) : θ x ∈ eigPart opB c := by
  rw [mem_eigPart] at hx ⊢
  intro i
  rw [← hI, hx i, map_smul]
end Formalism.IndefR.U2
