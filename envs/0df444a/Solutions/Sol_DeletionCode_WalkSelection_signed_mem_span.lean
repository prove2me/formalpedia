-- Prove2me | solution 1 for DeletionCode.WalkSelection.signed_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:14.714171+00:00
-- url     : https://prove2.me/submissions/7932f644-ba69-46f0-ba1a-37dd8ddaf3d0

import Definitions.Def_DeletionCode_ClosedWalk
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_DeletionCode_WalkSelection
import Theorems.Thm_DeletionCode_WalkSelection_selected_mem_span

set_option autoImplicit true
open DeletionCode DeletionCode.WalkSelection
open scoped BigOperators
variable {V : Type*} [AddCommGroup V] [Module ℚ V] {m : ℕ}
namespace DeletionCode.WalkSelection
theorem _root_.solution (step : Fin m → V) (S : Finset (Fin m))
    (v : V) (hv : SignedMember step S v) : v ∈ selectedSpan step S := by
  obtain ⟨r, hr, h | h⟩ := hv
  · rw [h]
    exact selected_mem_span step S r hr
  · rw [h]
    exact (selectedSpan step S).neg_mem (selected_mem_span step S r hr)
end DeletionCode.WalkSelection
