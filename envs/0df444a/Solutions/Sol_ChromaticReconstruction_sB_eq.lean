-- Prove2me | solution 1 for ChromaticReconstruction.sB_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:30:23.898581+00:00
-- url     : https://prove2.me/submissions/a183de59-af8a-4020-80ca-6065988d70b2

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
theorem _root_.solution {F : Finset (Sym2 (Fin (n + 1)))} {s : ℕ} (hs1 : 1 ≤ s) (hs2 : s ≤ c + 1)
    (hb : brk n c F s) (hmin : ∀ j, 1 ≤ j → j < s → ¬ brk n c F j) : sB n c F = s := by
  have h : HasBrk n c F := ⟨s, hs1, hs2, hb⟩
  unfold sB
  rw [dif_pos h]
  exact (Nat.find_eq_iff h).2 ⟨⟨hs1, hs2, hb⟩, fun j hj ⟨hj1, _, hjb⟩ => hmin j hj1 hj hjb⟩
end ChromaticReconstruction
