-- Prove2me | solution 1 for F6ConvexWindow.two_chain_degree_eq_A2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:54:18.352104+00:00
-- url     : https://prove2.me/submissions/69c66c05-042e-4c6c-b4f7-a3f77e89f269

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Theorems.Thm_F6ConvexWindow_mem_Inc
import Theorems.Thm_F6ConvexWindow_mem_ideal
import Theorems.Thm_F6ConvexWindow_mem_antichains
import Theorems.Thm_F6ConvexWindow_degree_pair_fiber
import Theorems.Thm_F6ConvexWindow_ChainDecomposition_mem_part
import Theorems.Thm_F6ConvexWindow_ChainDecomposition_full_antichain_fiber_card
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
theorem _root_.solution (d : ChainDecomposition (V := V) 2) (i : Fin 2) :
    (∑ x ∈ d.part i, (Inc x).card) = Ak (V := V) 2 := by
  classical
  let F := (antichains (V := V)).filter (fun T => T.card = 2)
  calc
    (∑ x ∈ d.part i, (Inc x).card) = ∑ x ∈ d.part i, (F.filter (fun T => x ∈ T)).card := by
      apply sum_congr rfl
      intro x hx
      exact degree_pair_fiber x
    _ = ∑ T ∈ F, ∑ x ∈ d.part i, if x ∈ T then 1 else 0 := by
      simp only [card_filter]
      rw [sum_comm]
    _ = ∑ T ∈ F, (T.filter (fun x => d.color x = i)).card := by
      apply sum_congr rfl
      intro T hT
      have hsets : (d.part i).filter (fun x => x ∈ T) =
          T.filter (fun x => d.color x = i) := by
        ext x
        simp only [mem_filter, ChainDecomposition.mem_part]
        exact and_comm
      have hcard :
          ((d.part i).filter (fun x => x ∈ T)).card =
            (T.filter (fun x => d.color x = i)).card :=
        congrArg Finset.card hsets
      simpa only [sum_boole, Nat.cast_id] using hcard
    _ = ∑ T ∈ F, 1 := by
      apply sum_congr rfl
      intro T hT
      exact d.full_antichain_fiber_card (mem_antichains.mp (mem_filter.mp hT).1)
        (mem_filter.mp hT).2 i
    _ = Ak (V := V) 2 := by simp [Ak, F]
end F6ConvexWindow
