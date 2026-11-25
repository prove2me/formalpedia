-- Prove2me | solution 1 for F6ConvexWindow.ChainDecomposition.mem_part
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:35:52.440492+00:00
-- url     : https://prove2.me/submissions/016effb4-31cb-480a-aa9b-6d1ddcaab55a

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Theorems.Thm_F6ConvexWindow_mem_Inc
import Theorems.Thm_F6ConvexWindow_mem_ideal
import Theorems.Thm_F6ConvexWindow_mem_antichains
attribute [local simp] F6ConvexWindow.mem_Inc
attribute [local simp] F6ConvexWindow.mem_ideal
attribute [local simp] F6ConvexWindow.mem_antichains

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
theorem _root_.solution {i : Fin k} {x : V} : x ∈ d.part i ↔ d.color x = i := by
  simp [part]
end F6ConvexWindow.ChainDecomposition
