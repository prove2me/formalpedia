-- Prove2me | solution 1 for ErdosPosa.IsMax023.no_cyc_R
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:32:39.000907+00:00
-- url     : https://prove2.me/submissions/4848c135-3fc2-4a2e-bdd1-f0e75dd0fe8d

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPPacking
public import Definitions.Def_ErdosPosaLib_EPMaximal
public import Theorems.Thm_ErdosPosa_neighborSet_empty_of_deg_zero
public import Theorems.Thm_ErdosPosa_not_adj_of_deg_zero
public import Theorems.Thm_ErdosPosa_restr_adj
attribute [local simp] ErdosPosa.restr_adj



set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}
variable [Finite V] {G H : SimpleGraph V}
namespace ErdosPosa
namespace IsMax023
theorem _root_.solution (hH : IsMax023 G H) : ¬ Cyc G {v | deg H v = 0} := by
  classical
  intro hc
  unfold Cyc IsAcyclic at hc
  push Not at hc
  obtain ⟨v, c, hc⟩ := hc
  let C : SimpleGraph V := c.toSubgraph.spanningCoe
  have hCadj : ∀ a b, C.Adj a b → (restr G {v | deg H v = 0}).Adj a b :=
    fun a b h => c.toSubgraph.adj_sub h
  have hCnbr : ∀ a, C.neighborSet a = c.toSubgraph.neighborSet a := fun a => rfl
  let K := H ⊔ C
  have hKG : K ≤ G := sup_le hH.1 (fun a b h => (hCadj a b h).1)
  have hdegK : ∀ a, deg K a = if a ∈ c.support then 2 else deg H a := by
    intro a
    rw [deg, neighborSet_sup]
    split_ifs with ha
    · have h2 := hc.ncard_neighborSet_toSubgraph_eq_two ha
      obtain ⟨b, hb⟩ : (c.toSubgraph.neighborSet a).Nonempty := by
        rw [← Set.ncard_pos (Set.toFinite _)]; omega
      have haR : deg H a = 0 := (hCadj a b hb).2.1
      rw [neighborSet_empty_of_deg_zero haR, Set.empty_union, hCnbr, h2]
    · have : C.neighborSet a = ∅ := by
        ext b
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hb
        exact ha ((c.mem_verts_toSubgraph).1 (Subgraph.Adj.fst_mem hb))
      rw [this, Set.union_empty]; rfl
  have hK : Deg023 K := by
    intro a; rw [hdegK a]; split_ifs
    · exact Or.inr (Or.inl rfl)
    · exact hH.2.1 a
  have hadj : C.Adj v c.snd := c.toSubgraph_adj_snd hc.not_nil
  have := hH.2.2 K hKG hK le_sup_left v c.snd (Or.inr hadj)
  exact not_adj_of_deg_zero (hCadj v c.snd hadj).2.1 this
end IsMax023
end ErdosPosa
