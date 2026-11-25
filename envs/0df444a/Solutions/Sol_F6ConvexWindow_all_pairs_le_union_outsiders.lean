-- Prove2me | solution 1 for F6ConvexWindow.all_pairs_le_union_outsiders
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:11:59.776925+00:00
-- url     : https://prove2.me/submissions/9a052818-8031-4650-8ebc-9ff07316c9f2

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
import Theorems.Thm_F6ConvexWindow_mem_tripleFamily
import Theorems.Thm_F6ConvexWindow_card_tripleFamily
import Theorems.Thm_F6ConvexWindow_mem_tripleUnion
import Theorems.Thm_F6ConvexWindow_mem_inducedPairs
import Theorems.Thm_F6ConvexWindow_pairCount_univ
import Theorems.Thm_F6ConvexWindow_pairCount_le_choose
import Theorems.Thm_F6ConvexWindow_card_crossPairs_le
import Theorems.Thm_F6ConvexWindow_crossPairs_mono
import Theorems.Thm_F6ConvexWindow_pairCount_union_le
import Theorems.Thm_F6ConvexWindow_outsider_neighbors_le_two
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
theorem _root_.solution (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    (F : Finset (Finset V)) (hf : ∀ T ∈ F, IsTriple T) :
    Ak (V := V) 2 ≤ pairCount (tripleUnion F) +
      2 * (univ \ tripleUnion F).card + (univ \ tripleUnion F).card.choose 2 := by
  classical
  let U := tripleUnion F
  let Q := (univ : Finset V) \ U
  have hcover : Q ∪ U = univ := by
    ext x
    by_cases hx : x ∈ U <;> simp [Q, hx]
  have hb := pairCount_union_le Q U
  rw [hcover, pairCount_univ] at hb
  have hQ := pairCount_le_choose Q
  have hcross := (card_le_card (crossPairs_mono (sdiff_subset : Q \ U ⊆ Q)
    (sdiff_subset : U \ Q ⊆ U))).trans (card_crossPairs_le Q U)
  have hrows := sum_le_sum (s := Q) (fun x hx => outsider_neighbors_le_two hw hci F hf
    (show x ∉ tripleUnion F from (mem_sdiff.mp hx).2))
  have hc : crossCount Q U ≤ 2 * Q.card := by
    simpa [crossCount, U, Nat.mul_comm] using hrows
  change Ak (V := V) 2 ≤ pairCount U + 2 * Q.card + Q.card.choose 2
  omega
end F6ConvexWindow
