-- Prove2me | solution 1 for Formalism.IndefR.U2.notLifted_le_ker
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:07:21.910529+00:00
-- url     : https://prove2.me/submissions/9b68df5b-b972-437c-9074-85a4943568ba

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_NormalDecomposition_DecompOfNormalStatement
import Theorems.Thm_Formalism_IndefR_U2_map_eigPart

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
theorem _root_.solution (hI : Intw θ op opB) (hG : GoodIn θ good goodB) {c : I → ℂ} (hc : c ∈ Ix)
    (hn : c ∉ Lifted opB goodB Ix) : eigPart op c ⊓ good ≤ LinearMap.ker θ := by
  intro x hx
  have h0 : eigPart opB c ⊓ goodB = ⊥ := by
    by_contra h
    exact hn ⟨hc, h⟩
  have hm : θ x ∈ eigPart opB c ⊓ goodB := ⟨map_eigPart hI hx.1, hG x hx.2⟩
  rw [h0, Submodule.mem_bot] at hm
  exact hm
end Formalism.IndefR.U2
