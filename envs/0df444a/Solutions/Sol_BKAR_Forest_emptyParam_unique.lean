-- Prove2me | solution 1 for BKAR.Forest.emptyParam_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:43:50.93254+00:00
-- url     : https://prove2.me/submissions/18cc7fcc-1210-410d-a181-029ce477b5ed

import Mathlib.Data.Real.Basic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_Interpolation
import Theorems.Thm_BKAR_Forest_empty_edges


set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (u : (Forest.empty V).EdgeParam → ℝ) :
    u = emptyParam := by
  funext e
  exact False.elim (by
    have he : e.val ∈ (∅ : Finset (Edge V)) := by
      rw [← Forest.empty_edges V]
      exact e.property
    exact Finset.notMem_empty e.val he)
end BKAR.Forest
