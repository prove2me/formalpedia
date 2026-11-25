-- Prove2me | solution 1 for ErdosPosa.cyc_glue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:23:27.786528+00:00
-- url     : https://prove2.me/submissions/1e8bd063-3beb-4784-a39f-a3b25c1c04a6

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPCyc
public import Theorems.Thm_ErdosPosa_restr_adj
public import Theorems.Thm_ErdosPosa_reach_transfer
public import Theorems.Thm_ErdosPosa_cyc_iff
public import Theorems.Thm_ErdosPosa_deleteEdges_adj_iff
attribute [local simp] ErdosPosa.restr_adj

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}
namespace ErdosPosa
theorem _root_.solution {H : SimpleGraph V} {X Y : Set V} (h : Cyc H (X ∪ Y))
    (hcross : ∀ a b, a ∈ X → a ∉ Y → b ∈ Y → b ∉ X → ¬ H.Adj a b)
    (hint : ∀ a b, a ∈ X → a ∈ Y → b ∈ X → b ∈ Y → a = b) : Cyc H X ∨ Cyc H Y := by
  classical
  -- general statement for one side
  have side : ∀ (X Y : Set V), (∀ a b, a ∈ X → a ∉ Y → b ∈ Y → b ∉ X → ¬ H.Adj a b) →
      (∀ a b, a ∈ X → a ∈ Y → b ∈ X → b ∈ Y → a = b) → ∀ u v, u ∈ X → v ∈ X →
      (restr H (X ∪ Y)).Adj u v →
      ((restr H (X ∪ Y)).deleteEdges {s(u, v)}).Reachable u v → Cyc H X := by
    intro X Y hcross hint u v hu hv huv hr
    rw [cyc_iff]
    let p : V := if hp : ∃ z, z ∈ X ∧ z ∈ Y then hp.choose else u
    have hpX : p ∈ X := by
      by_cases hp : ∃ z, z ∈ X ∧ z ∈ Y
      · simp only [p, hp, dite_true]; exact hp.choose_spec.1
      · simp only [p, hp, dite_false]; exact hu
    have hpeq : ∀ z, z ∈ X → z ∈ Y → p = z := by
      intro z hzX hzY
      have hp : ∃ z, z ∈ X ∧ z ∈ Y := ⟨z, hzX, hzY⟩
      simp only [p, hp, dite_true]
      exact hint _ _ hp.choose_spec.1 hp.choose_spec.2 hzX hzY
    let f : V → V := fun y => if y ∈ X then y else p
    have hfu : f u = u := by simp [f, hu]
    have hfv : f v = v := by simp [f, hv]
    refine ⟨u, v, ⟨huv.1, hu, hv⟩, ?_⟩
    have := reach_transfer (G2 := (restr H X).deleteEdges {s(u, v)}) f ?_ hr
    · rwa [hfu, hfv] at this
    intro a b hab
    rw [deleteEdges_adj_iff] at hab
    obtain ⟨⟨hab, ha, hb⟩, hne⟩ := hab
    by_cases haX : a ∈ X
    · by_cases hbX : b ∈ X
      · simp only [f, haX, hbX, ite_true]
        apply Adj.reachable
        rw [deleteEdges_adj_iff]
        exact ⟨⟨hab, haX, hbX⟩, hne⟩
      · have hbY : b ∈ Y := hb.resolve_left hbX
        have haY : a ∈ Y := by
          by_contra haY; exact hcross a b haX haY hbY hbX hab
        simp only [f, haX, hbX, ite_true, ite_false]
        rw [hpeq a haX haY]
    · by_cases hbX : b ∈ X
      · have haY : a ∈ Y := ha.resolve_left haX
        have hbY : b ∈ Y := by
          by_contra hbY; exact hcross b a hbX hbY haY haX hab.symm
        simp only [f, haX, hbX, ite_true, ite_false]
        rw [hpeq b hbX hbY]
      · simp only [f, haX, hbX, ite_false]; rfl
  rw [cyc_iff] at h
  obtain ⟨u, v, huv, hr⟩ := h
  have hu := huv.2.1
  have hv := huv.2.2
  by_cases huX : u ∈ X
  · by_cases hvX : v ∈ X
    · exact Or.inl (side X Y hcross hint u v huX hvX huv hr)
    · have hvY : v ∈ Y := hv.resolve_left hvX
      have huY : u ∈ Y := by
        by_contra huY; exact hcross u v huX huY hvY hvX huv.1
      right
      refine side Y X (fun a b ha hna hb hnb => fun hab => hcross b a hb hnb ha hna hab.symm)
        (fun a b h1 h2 h3 h4 => hint a b h2 h1 h4 h3) u v huY hvY ?_ ?_
      · rw [Set.union_comm]; exact huv
      · rw [Set.union_comm]; exact hr
  · have huY : u ∈ Y := hu.resolve_left huX
    by_cases hvY : v ∈ Y
    · right
      refine side Y X (fun a b ha hna hb hnb => fun hab => hcross b a hb hnb ha hna hab.symm)
        (fun a b h1 h2 h3 h4 => hint a b h2 h1 h4 h3) u v huY hvY ?_ ?_
      · rw [Set.union_comm]; exact huv
      · rw [Set.union_comm]; exact hr
    · have hvX : v ∈ X := hv.resolve_right hvY
      exact absurd huv.1.symm (hcross v u hvX hvY huY huX)
end ErdosPosa
