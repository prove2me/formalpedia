-- Prove2me | solution 1 for F6ConvexWindow.totalAntichains_le_46_of_six_triples
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:25:52.966207+00:00
-- url     : https://prove2.me/submissions/0bd94b7d-ecfc-4a1b-8d0e-7035eb544d85

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
import Theorems.Thm_F6ConvexWindow_mem_tripleFamily
import Theorems.Thm_F6ConvexWindow_card_tripleFamily
import Theorems.Thm_F6ConvexWindow_mem_tripleUnion
import Theorems.Thm_F6ConvexWindow_mem_inducedPairs
import Theorems.Thm_F6ConvexWindow_triple_union_counts
import Theorems.Thm_F6ConvexWindow_all_pairs_le_union_outsiders
import Theorems.Thm_F6ConvexWindow_n15_large_triple_arithmetic
import Theorems.Thm_F6ConvexWindowFull_T1
import Theorems.Thm_F6ConvexWindow_ChainDecomposition_mem_part
import Theorems.Thm_F6ConvexWindow_antichain_count_width3
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
    (hn : Fintype.card V = 15) (ht : 6 ≤ Ak (V := V) 3) : totalAntichains (V := V) ≤ 46 := by
  classical
  let F := tripleFamily (V := V)
  let U := tripleUnion F
  let Q := (univ : Finset V) \ U
  have hf : ∀ T ∈ F, IsTriple T := fun T hT => mem_tripleFamily.mp hT
  have hFc : F.card = Ak (V := V) 3 := card_tripleFamily
  have hFn : F.Nonempty := card_pos.mp (by omega)
  have htop := F6ConvexWindowFull.T1 hw hci (show 0 < Ak (V := V) 3 by omega)
  rw [hn] at htop
  obtain ⟨huc, hec⟩ := triple_union_counts hw hci F hf hFn
  have hpart : U.card + Q.card = Fintype.card V := by
    have h := card_sdiff_add_card_eq_card (subset_univ U)
    simpa [Q, Nat.add_comm] using h
  have hsize : 2 * Ak (V := V) 3 + 1 + emptyTransitions F + Q.card = 15 := by
    change U.card = 2 * F.card + 1 + emptyTransitions F at huc
    omega
  have he := all_pairs_le_union_outsiders hw hci F hf
  have he' : Ak (V := V) 2 ≤ 3 * Ak (V := V) 3 + 3 * emptyTransitions F +
      2 * Q.card + Q.card.choose 2 := by
    change Ak (V := V) 2 ≤ pairCount U + 2 * Q.card + Q.card.choose 2 at he
    change pairCount U ≤ 3 * F.card + 3 * emptyTransitions F at hec
    omega
  have htrade := n15_large_triple_arithmetic _ _ _ _ ht htop hsize he'
  have hcount := antichain_count_width3 hw
  omega
end F6ConvexWindow
