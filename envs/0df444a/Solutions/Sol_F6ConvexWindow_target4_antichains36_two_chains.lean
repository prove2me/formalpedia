-- Prove2me | solution 1 for F6ConvexWindow.target4_antichains36_two_chains
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:01:36.226567+00:00
-- url     : https://prove2.me/submissions/ecc4cf46-bf90-40d6-8e94-6c4608f6497b

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Theorems.Thm_F6ConvexWindow_mem_Inc
import Theorems.Thm_F6ConvexWindow_mem_ideal
import Theorems.Thm_F6ConvexWindow_mem_antichains
import Theorems.Thm_F6ConvexWindow_chain_degree_bound
import Theorems.Thm_F6ConvexWindow_antichain_count_width2
import Theorems.Thm_F6ConvexWindow_ChainDecomposition_mem_part
import Theorems.Thm_F6ConvexWindow_ChainDecomposition_parts_card
import Theorems.Thm_F6ConvexWindow_two_chain_degree_eq_A2
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
theorem _root_.solution (hw : WidthLE (V := V) 2) (hci : CI2 (V := V))
    (hn : Fintype.card V ≤ 15) (d : ChainDecomposition (V := V) 2) :
    totalAntichains (V := V) ≤ 36 := by
  classical
  have he := antichain_count_width2 hw
  have hrow0 := two_chain_degree_eq_A2 d 0
  have hrow1 := two_chain_degree_eq_A2 d 1
  by_cases h0 : (d.part 0).Nonempty
  · by_cases h1 : (d.part 1).Nonempty
    · have hb0 := chain_degree_bound hci (d.chain_fiber 0) h0
      have hb1 := chain_degree_bound hci (d.chain_fiber 1) h1
      change (∑ x ∈ d.part 0, (Inc x).card) + 2 ≤ Fintype.card V + (d.part 0).card at hb0
      change (∑ x ∈ d.part 1, (Inc x).card) + 2 ≤ Fintype.card V + (d.part 1).card at hb1
      rw [hrow0] at hb0
      rw [hrow1] at hb1
      have hp := d.parts_card
      simp only [Fin.sum_univ_two] at hp
      omega
    · have hempty := not_nonempty_iff_eq_empty.mp h1
      rw [hempty, sum_empty] at hrow1
      omega
  · have hempty := not_nonempty_iff_eq_empty.mp h0
    rw [hempty, sum_empty] at hrow0
    omega
end F6ConvexWindow
