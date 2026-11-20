-- Prove2me | solution 1 for DeletionCode.WalkSelection.selected_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:15:58.04633+00:00
-- url     : https://prove2.me/submissions/2d933956-f8be-43d8-9b36-4805983fe6e4

import Definitions.Def_DeletionCode_ClosedWalk
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_DeletionCode_WalkSelection

set_option autoImplicit true
open DeletionCode DeletionCode.WalkSelection
open scoped BigOperators
variable {V : Type*} [AddCommGroup V] [Module ℚ V] {m : ℕ}
namespace DeletionCode.WalkSelection
theorem _root_.solution (step : Fin m → V) (S : Finset (Fin m))
    (r : Fin m) (hr : r ∈ S) : step r ∈ selectedSpan step S :=
  Submodule.subset_span ⟨r, hr, rfl⟩
end DeletionCode.WalkSelection
