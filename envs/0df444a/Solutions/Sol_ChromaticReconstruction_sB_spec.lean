-- Prove2me | solution 1 for ChromaticReconstruction.sB_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T12:54:01.605311+00:00
-- url     : https://prove2.me/submissions/d3c78961-9c29-452f-96bd-0261effc1438

import Definitions.Def_RequestProject_PathLeaf
import Definitions.Def_RequestProject_Truncation
import Definitions.Def_RequestProject_PathLeafSwap

set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {n c : ℕ}
namespace ChromaticReconstruction
theorem _root_.solution {F : Finset (Sym2 (Fin (n + 1)))} (h : HasBrk n c F) :
    1 ≤ sB n c F ∧ sB n c F ≤ c + 1 ∧ brk n c F (sB n c F) ∧
      ∀ j, 1 ≤ j → j < sB n c F → ¬ brk n c F j := by
  unfold sB
  rw [dif_pos h]
  obtain ⟨h1, h2, h3⟩ := Nat.find_spec h
  refine ⟨h1, h2, h3, fun j hj hjs hb => ?_⟩
  exact Nat.find_min h hjs ⟨hj, by omega, hb⟩
end ChromaticReconstruction
