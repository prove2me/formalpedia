-- Prove2me | solution 1 for BrooksTheorem.Aux.glue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:32:47.399262+00:00
-- url     : https://prove2.me/submissions/d89a8121-ec79-478b-8cbf-d33742b7a0f8

module
public import Definitions.Def_BrooksLib_Greedy
public import Definitions.Def_BrooksLib_BrooksCore
public import Theorems.Thm_BrooksTheorem_Aux_restr_adj
public import Theorems.Thm_BrooksTheorem_Aux_mem_nb
attribute [local simp] BrooksTheorem.Aux.mem_nb


attribute [local simp] BrooksTheorem.Aux.restr_adj

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BrooksTheorem
open BrooksTheorem.Aux
variable {V : Type*}
namespace BrooksTheorem.Aux
theorem _root_.solution {k : ℕ} (H : SimpleGraph V) (S1 S2 : Set V)
    (hedge : ∀ u v, H.Adj u v → (u ∈ S1 ∧ v ∈ S1) ∨ (u ∈ S2 ∧ v ∈ S2))
    (c1 c2 : V → Fin k) (h1 : Proper (restr H S1) c1) (h2 : Proper (restr H S2) c2)
    (hagree : ∀ v ∈ S1, v ∈ S2 → c1 v = c2 v) : ∃ g : V → Fin k, Proper H g := by
  classical
  refine ⟨fun v => if v ∈ S1 then c1 v else c2 v, fun u v huv => ?_⟩
  rcases hedge u v huv with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · simp only [hu, hv, ite_true]
    exact h1 u v ⟨huv, hu, hv⟩
  · have eu : (if u ∈ S1 then c1 u else c2 u) = c2 u := by
      split_ifs with h
      · exact hagree u h hu
      · rfl
    have ev : (if v ∈ S1 then c1 v else c2 v) = c2 v := by
      split_ifs with h
      · exact hagree v h hv
      · rfl
    simp only [eu, ev]
    exact h2 u v ⟨huv, hu, hv⟩
end BrooksTheorem.Aux
