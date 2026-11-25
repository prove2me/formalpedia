-- Prove2me | solution 1 for F6ConvexWindow.chain_cover_to_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:09:42.452771+00:00
-- url     : https://prove2.me/submissions/5d8ca168-da15-44dd-a14e-62fdb2330e41

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_DilworthTheorem
import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Theorems.Thm_F6ConvexWindow_ChainDecomposition_mem_part
import Theorems.Thm_F6ConvexWindow_mem_Inc
import Theorems.Thm_F6ConvexWindow_mem_antichains
import Theorems.Thm_F6ConvexWindow_mem_ideal
attribute [local simp] F6ConvexWindow.ChainDecomposition.mem_part
attribute [local simp] F6ConvexWindow.mem_Inc
attribute [local simp] F6ConvexWindow.mem_antichains
attribute [local simp] F6ConvexWindow.mem_ideal



set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
variable {V : Type*} [Fintype V] [PartialOrder V]
namespace F6ConvexWindow
theorem _root_.solution {k : ℕ} (C : Fin k → Finset V)
    (hC : DilworthTheorem.IsChainCover (univ : Finset V) C) :
    Nonempty (ChainDecomposition (V := V) k) := by
  classical
  have hcover (x : V) : ∃ i, x ∈ C i := by
    have hx : x ∈ univ.biUnion C := hC.2.1.symm ▸ mem_univ x
    simpa only [mem_biUnion, mem_univ, true_and] using hx
  choose color hcolor using hcover
  refine ⟨⟨color, ?_⟩⟩
  intro i x hx y hy
  have hxi : color x = i := (mem_filter.mp hx).2
  have hyi : color y = i := (mem_filter.mp hy).2
  exact hC.1 i x y (hxi ▸ hcolor x) (hyi ▸ hcolor y)
end F6ConvexWindow
