-- Prove2me | solution 1 for ChromaticReconstruction.eq_pair_of_compType
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:15:32.679566+00:00
-- url     : https://prove2.me/submissions/23c80af0-9662-4c07-9e77-a98183e1c532

import Definitions.Def_RequestProject_PhiFormula
import Definitions.Def_RequestProject_CompStructure
import Theorems.Thm_ChromaticReconstruction_compOf_mem
import Theorems.Thm_ChromaticReconstruction_mem_compOf_self
import Theorems.Thm_ChromaticReconstruction_mem_compType
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
import Theorems.Thm_ChromaticReconstruction_mem_compSets_of_reachable
import Theorems.Thm_ChromaticReconstruction_reachable_of_mem
import Theorems.Thm_ChromaticReconstruction_reachable_of_mem_compSets
attribute [local simp] ChromaticReconstruction.killP1_X_one



set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]
namespace ChromaticReconstruction
theorem _root_.solution {A : Finset (Sym2 V)} (hA : ∀ e ∈ A, ¬ e.IsDiag) {s : ℕ}
    (h : compType (A : Set (Sym2 V)) = 2 ::ₘ Multiset.replicate s 1) :
    ∃ u v, u ≠ v ∧ A = {s(u, v)} := by
  have hle : ∀ C ∈ compSets (A : Set (Sym2 V)), C.card ≤ 2 := by
    intro C hC
    have : C.card ∈ compType (A : Set (Sym2 V)) := mem_compType.2 ⟨C, hC, rfl⟩
    rw [h, Multiset.mem_cons, Multiset.mem_replicate] at this
    omega
  obtain ⟨B, hB, hB2⟩ : ∃ B ∈ compSets (A : Set (Sym2 V)), B.card = 2 :=
    mem_compType.1 (by rw [h]; exact Multiset.mem_cons_self _ _)
  have huniq : ∀ C ∈ compSets (A : Set (Sym2 V)), C.card = 2 → C = B := by
    intro C hC hC2
    by_contra hne
    have hcount : 2 ≤ Multiset.count 2 (compType (A : Set (Sym2 V))) := by
      rw [compType, Multiset.count_map]
      have hsub : ({B, C} : Finset (Finset V)).val ≤
          (compSets (A : Set (Sym2 V))).val.filter (fun x => 2 = x.card) := by
        rw [← filter_val]
        apply val_le_iff.2
        intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl <;> simp [*]
      have := Multiset.card_le_card hsub
      rw [card_val, card_pair (Ne.symm hne)] at this
      exact this
    rw [h, Multiset.count_cons_self, Multiset.count_replicate] at hcount
    simp at hcount
  obtain ⟨u, v, huv, rfl⟩ := card_eq_two.1 hB2
  -- every edge of `A` joins `u` and `v`
  have hedge : ∀ e ∈ A, e = s(u, v) := by
    intro e he
    induction e using Sym2.ind with
    | _ x y =>
      have hxy : x ≠ y := fun h' => hA _ he (by simp [h'])
      have hC := compOf_mem (A : Set (Sym2 V)) x
      have hy : y ∈ compOf (A : Set (Sym2 V)) x :=
        mem_compSets_of_reachable hC (mem_compOf_self _ x) (reachable_of_mem (by exact he))
      have h2 : ({x, y} : Finset V).card ≤ (compOf (A : Set (Sym2 V)) x).card :=
        card_le_card (by
          intro z hz
          simp only [mem_insert, mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact mem_compOf_self _ _
          · exact hy)
      rw [card_pair hxy] at h2
      have hc2 := le_antisymm (hle _ hC) h2
      have hxyC : compOf (A : Set (Sym2 V)) x = {x, y} :=
        (eq_of_subset_of_card_le (by
          intro z hz
          simp only [mem_insert, mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact mem_compOf_self _ _
          · exact hy) (by rw [hc2, card_pair hxy])).symm
      have := huniq _ hC hc2
      rw [hxyC] at this
      have hx : x ∈ ({u, v} : Finset V) := this ▸ mem_insert_self x {y}
      have hy' : y ∈ ({u, v} : Finset V) := this ▸ mem_insert_of_mem (mem_singleton_self y)
      simp only [mem_insert, mem_singleton] at hx hy'
      rcases hx with rfl | rfl <;> rcases hy' with rfl | rfl
      · exact absurd rfl hxy
      · rfl
      · exact Sym2.eq_swap
      · exact absurd rfl hxy
  refine ⟨u, v, huv, ?_⟩
  -- `A` is nonempty since `u` and `v` are connected
  have hne : A.Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro hA0
    have := reachable_of_mem_compSets hB (mem_insert_self u {v})
      (mem_insert_of_mem (mem_singleton_self v))
    rw [hA0, coe_empty, SimpleGraph.fromEdgeSet_empty] at this
    exact huv (SimpleGraph.reachable_bot.1 this)
  obtain ⟨e, he⟩ := hne
  ext z
  simp only [mem_singleton]
  constructor
  · exact hedge z
  · rintro rfl; rw [← hedge e he]; exact he
end ChromaticReconstruction
