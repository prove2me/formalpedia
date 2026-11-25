-- Prove2me | solution 1 for F6ConvexWindow.ChainDecomposition.color_injective_on_antichain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:05:56.377833+00:00
-- url     : https://prove2.me/submissions/55f7cfa8-0c3d-4f83-a1ea-d0d4c495e1d4

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Theorems.Thm_F6ConvexWindow_ChainDecomposition_mem_part
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
theorem _root_.solution {T : Finset V} (ht : Antichain T) :
    Set.InjOn d.color T := by
  intro x hx y hy he
  have hxP : x ∈ d.part (d.color x) := (mem_part d).mpr rfl
  have hyP : y ∈ d.part (d.color x) := (mem_part d).mpr he.symm
  exact ((d.chain_fiber (d.color x)) x hxP y hyP).elim
    (ht x hx y hy) (fun h => (ht y hy x hx h).symm)
end F6ConvexWindow.ChainDecomposition
