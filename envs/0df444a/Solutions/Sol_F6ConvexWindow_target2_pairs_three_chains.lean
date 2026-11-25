-- Prove2me | solution 1 for F6ConvexWindow.target2_pairs_three_chains
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:59:43.457167+00:00
-- url     : https://prove2.me/submissions/711a45a6-db10-4c4a-a3e9-2dc03aa0fd1b

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Theorems.Thm_F6ConvexWindow_mem_Inc
import Theorems.Thm_F6ConvexWindow_mem_ideal
import Theorems.Thm_F6ConvexWindow_mem_antichains
import Theorems.Thm_F6ConvexWindow_chain_degree_bound
import Theorems.Thm_F6ConvexWindow_degree_sum_eq_twice_A2
import Theorems.Thm_F6ConvexWindow_ChainDecomposition_mem_part
import Theorems.Thm_F6ConvexWindow_ChainDecomposition_parts_card
import Theorems.Thm_F6ConvexWindow_ChainDecomposition_parts_sum
import Theorems.Thm_F6ConvexWindow_ChainDecomposition_part_nonempty_of_full_antichain
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
namespace F6ConvexWindow
theorem _root_.solution (_hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    (hpos : 0 < Ak (V := V) 3) (d : ChainDecomposition (V := V) 3) :
    Ak (V := V) 2 + 3 ≤ 2 * Fintype.card V := by
  classical
  obtain ⟨T, hT⟩ := card_pos.mp hpos
  have ht : Antichain T := mem_antichains.mp (mem_filter.mp hT).1
  have htc : T.card = 3 := (mem_filter.mp hT).2
  have hb (i : Fin 3) : (∑ x ∈ d.part i, (Inc x).card) + 2 ≤
      Fintype.card V + (d.part i).card := chain_degree_bound hci (d.chain_fiber i)
    (d.part_nonempty_of_full_antichain ht htc i)
  have hsum := sum_le_sum (s := (univ : Finset (Fin 3))) (fun i _ => hb i)
  simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  rw [d.parts_sum, degree_sum_eq_twice_A2, d.parts_card] at hsum
  omega
end F6ConvexWindow
