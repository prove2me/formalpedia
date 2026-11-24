-- Prove2me | solution 1 for FairSelling.config_loss_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:04:13.85554+00:00
-- url     : https://prove2.me/submissions/91930817-e563-467f-a679-41c74d6228bf

import Mathlib
import Definitions.Def_RequestProject_MatchingPhase
import Definitions.Def_RequestProject_ConfigSplit
import Theorems.Thm_FairSelling_sum_price_le_vbarSum
import Theorems.Thm_FairSelling_cashPrice_none
import Theorems.Thm_FairSelling_cashPrice_some
import Theorems.Thm_FairSelling_cashVal_none
import Theorems.Thm_FairSelling_cashVal_some
import Theorems.Thm_FairSelling_fin3_cover
import Theorems.Thm_FairSelling_mem_optionGoods
import Theorems.Thm_FairSelling_restrictVal_mem
import Theorems.Thm_FairSelling_vbarSum_union
attribute [local simp] FairSelling.cashPrice_none
attribute [local simp] FairSelling.cashPrice_some
attribute [local simp] FairSelling.cashVal_none
attribute [local simp] FairSelling.cashVal_some
attribute [local simp] FairSelling.mem_optionGoods
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {A : Fin 3 → Finset G} {s : Finset G} {q : Fin 3 → ℝ} {r : ℝ}
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) (hcfg : ConfigN 3 w p r A s q) (X : Finset G)
    {j j' j'' : Fin 3} (h1 : j ≠ j') (h2 : j ≠ j'') (h3 : j' ≠ j'') :
    vbarSum w p (A j ∩ X) + vbarSum w p ((A j' ∪ A j'') ∩ X) + ∑ g ∈ s ∩ X, p g
      ≤ vbarSum w p X := by
  classical
  obtain ⟨hdisjA, hdisjs, hcover, -⟩ := hcfg
  have hmem : ∀ x : G, x ∈ s ∨ x ∈ A j ∨ x ∈ A j' ∨ x ∈ A j'' := by
    intro x
    have hx : x ∈ s ∪ Finset.univ.biUnion A := by rw [hcover]; exact Finset.mem_univ x
    rcases Finset.mem_union.mp hx with h | h
    · exact Or.inl h
    · obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp h
      rcases fin3_cover h1 h2 h3 i with rfl | rfl | rfl
      · exact Or.inr (Or.inl hi)
      · exact Or.inr (Or.inr (Or.inl hi))
      · exact Or.inr (Or.inr (Or.inr hi))
  have hsplit : X = (A j ∩ X) ∪ ((A j' ∪ A j'') ∩ X) ∪ (s ∩ X) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · intro hx
      rcases hmem x with h | h | h | h
      · exact Or.inr ⟨h, hx⟩
      · exact Or.inl (Or.inl ⟨h, hx⟩)
      · exact Or.inl (Or.inr ⟨Or.inl h, hx⟩)
      · exact Or.inl (Or.inr ⟨Or.inr h, hx⟩)
    · rintro ((⟨-, hx⟩ | ⟨-, hx⟩) | ⟨-, hx⟩) <;> exact hx
  have hd1 : Disjoint (A j ∩ X) ((A j' ∪ A j'') ∩ X) := by
    refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
    have hxj := (Finset.mem_inter.mp hx).1
    rcases Finset.mem_union.mp (Finset.mem_inter.mp hx').1 with h | h
    · exact (Finset.disjoint_left.mp (hdisjA j j' h1)) hxj h
    · exact (Finset.disjoint_left.mp (hdisjA j j'' h2)) hxj h
  have hd2 : Disjoint ((A j ∩ X) ∪ ((A j' ∪ A j'') ∩ X)) (s ∩ X) := by
    refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
    have hxs := (Finset.mem_inter.mp hx').1
    rcases Finset.mem_union.mp hx with h | h
    · exact (Finset.disjoint_left.mp (hdisjs j)) hxs (Finset.mem_inter.mp h).1
    · rcases Finset.mem_union.mp (Finset.mem_inter.mp h).1 with h' | h'
      · exact (Finset.disjoint_left.mp (hdisjs j')) hxs h'
      · exact (Finset.disjoint_left.mp (hdisjs j'')) hxs h'
  have hle := sum_price_le_vbarSum w p (s ∩ X)
  have hval : vbarSum w p X
      = vbarSum w p (A j ∩ X) + vbarSum w p ((A j' ∪ A j'') ∩ X) + vbarSum w p (s ∩ X) := by
    conv_lhs => rw [hsplit]
    rw [vbarSum_union w p hd2, vbarSum_union w p hd1]
  linarith
end FairSelling
