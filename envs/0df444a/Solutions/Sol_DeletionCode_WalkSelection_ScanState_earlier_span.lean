-- Prove2me | solution 1 for DeletionCode.WalkSelection.ScanState.earlier_span
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:18:39.338722+00:00
-- url     : https://prove2.me/submissions/dc5833f3-d257-4b98-832b-894d2ef29745

import Definitions.Def_DeletionCode_ClosedWalk
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_DeletionCode_WalkSelection
import Theorems.Thm_DeletionCode_WalkSelection_signed_mem_span

set_option autoImplicit true
open DeletionCode DeletionCode.WalkSelection
open scoped BigOperators
variable {V : Type*} [AddCommGroup V] [Module ℚ V] {m : ℕ}
namespace DeletionCode.WalkSelection
namespace ScanState
theorem _root_.solution {step : Fin m → V} {Good : Finset (Fin m) → Prop}
    {n : ℕ} {S : Finset (Fin m)} (h : ScanState step Good n S)
    (j : Fin m) (hj : j.val < n) : step j ∈ selectedSpan step S := by
  obtain ⟨r, hr, _, heq⟩ := h.covered j hj
  exact signed_mem_span step S (step j) ⟨r, hr, heq⟩
end ScanState
end DeletionCode.WalkSelection
