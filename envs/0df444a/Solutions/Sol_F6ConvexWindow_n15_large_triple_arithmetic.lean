-- Prove2me | solution 1 for F6ConvexWindow.n15_large_triple_arithmetic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:06:35.9603+00:00
-- url     : https://prove2.me/submissions/2183e757-21e6-4bc7-a9d7-6862a175695a

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
import Theorems.Thm_F6ConvexWindow_mem_tripleFamily
import Theorems.Thm_F6ConvexWindow_card_tripleFamily
import Theorems.Thm_F6ConvexWindow_mem_tripleUnion
import Theorems.Thm_F6ConvexWindow_mem_inducedPairs
import Theorems.Thm_F6ConvexWindow_ChainDecomposition_mem_part
import Theorems.Thm_F6ConvexWindow_mem_Inc
import Theorems.Thm_F6ConvexWindow_mem_antichains
import Theorems.Thm_F6ConvexWindow_mem_ideal
attribute [local simp] F6ConvexWindow.ChainDecomposition.mem_part
attribute [local simp] F6ConvexWindow.mem_Inc
attribute [local simp] F6ConvexWindow.mem_antichains
attribute [local simp] F6ConvexWindow.mem_ideal


attribute [local simp] F6ConvexWindow.mem_tripleFamily
attribute [local simp] F6ConvexWindow.card_tripleFamily
attribute [local simp] F6ConvexWindow.mem_tripleUnion
attribute [local simp] F6ConvexWindow.mem_inducedPairs

set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]
namespace F6ConvexWindow
theorem _root_.solution (t m q e : ℕ) (ht : 6 ≤ t) (htop : 2 * t + 1 ≤ 15)
    (hn : 2 * t + 1 + m + q = 15)
    (he : e ≤ 3 * t + 3 * m + 2 * q + q.choose 2) : e + t ≤ 30 := by
  have hcases : t = 6 ∨ t = 7 := by omega
  rcases hcases with rfl | rfl
  · have hq : q = 0 ∨ q = 1 ∨ q = 2 := by omega
    rcases hq with rfl | rfl | rfl <;> norm_num at he <;> omega
  · have hm : m = 0 := by omega
    have hq : q = 0 := by omega
    simp only [hm, hq] at he
    norm_num at he
    omega
end F6ConvexWindow
