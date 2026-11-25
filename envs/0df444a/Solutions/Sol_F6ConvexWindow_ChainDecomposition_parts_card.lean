-- Prove2me | solution 1 for F6ConvexWindow.ChainDecomposition.parts_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:05:31.896994+00:00
-- url     : https://prove2.me/submissions/4a65efcb-aed7-4943-9bb4-20c2dd40b666

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Theorems.Thm_F6ConvexWindow_mem_Inc
import Theorems.Thm_F6ConvexWindow_mem_ideal
import Theorems.Thm_F6ConvexWindow_mem_antichains
import Theorems.Thm_F6ConvexWindow_ChainDecomposition_mem_part
attribute [local simp] F6ConvexWindow.mem_Inc
attribute [local simp] F6ConvexWindow.mem_ideal
attribute [local simp] F6ConvexWindow.mem_antichains
attribute [local simp] F6ConvexWindow.ChainDecomposition.mem_part

set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]
open F6ConvexWindow.ChainDecomposition
variable {k : ℕ} (d : ChainDecomposition (V := V) k)
namespace F6ConvexWindow.ChainDecomposition
theorem _root_.solution : (∑ i, (d.part i).card) = Fintype.card V := by
  simpa [part] using
    (card_eq_sum_card_fiberwise (s := (univ : Finset V)) (t := (univ : Finset (Fin k)))
      (f := d.color) (fun x hx => mem_univ (d.color x))).symm
end F6ConvexWindow.ChainDecomposition
