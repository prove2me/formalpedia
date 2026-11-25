-- Prove2me | solution 1 for ErdosPosa.cyc_remove_low
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:22:21.188188+00:00
-- url     : https://prove2.me/submissions/f9986256-df92-4fb7-b3dd-05b8760c7edf

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPCyc
public import Theorems.Thm_ErdosPosa_restr_adj
public import Theorems.Thm_ErdosPosa_reach_transfer
public import Theorems.Thm_ErdosPosa_reach_of_isolated
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
theorem _root_.solution {H : SimpleGraph V} {S : Set V} {x : V} (h : Cyc H S)
    (hx : ∀ y z, y ∈ S → z ∈ S → H.Adj x y → H.Adj x z → y = z) : Cyc H (S \ {x}) := by
  classical
  rw [cyc_iff] at h ⊢
  obtain ⟨u, v, huv, hr⟩ := h
  -- `x` is not an endpoint of the chosen non-bridge edge
  have key : ∀ {a b : V}, (restr H S).Adj a b →
      ((restr H S).deleteEdges {s(a, b)}).Reachable a b → a ≠ x := by
    rintro a b hab hr' rfl
    have := reach_of_isolated (G := (restr H S).deleteEdges {s(a, b)}) ?_ hr'
    · exact hab.1.ne this
    intro z hz
    rw [deleteEdges_adj_iff] at hz
    obtain ⟨⟨hz, -, hzS⟩, hne⟩ := hz
    have := hx z b hzS hab.2.2 hz hab.1
    subst this
    exact hne rfl
  have hux : u ≠ x := key huv hr
  have hvx : v ≠ x := by
    refine key huv.symm ?_
    have : s(v, u) = s(u, v) := Sym2.eq_swap
    rw [this]; exact hr.symm
  let p : V := if hp : ∃ y ∈ S, H.Adj x y then hp.choose else u
  let f : V → V := fun y => if y = x then p else y
  have hfu : f u = u := by simp [f, hux]
  have hfv : f v = v := by simp [f, hvx]
  refine ⟨u, v, ⟨huv.1, ⟨huv.2.1, hux⟩, ⟨huv.2.2, hvx⟩⟩, ?_⟩
  have := reach_transfer (G2 := (restr H (S \ {x})).deleteEdges {s(u, v)}) f ?_ hr
  · rwa [hfu, hfv] at this
  intro a b hab
  rw [deleteEdges_adj_iff] at hab
  obtain ⟨⟨hab, ha, hb⟩, hne⟩ := hab
  have hpn : ∀ y, y ∈ S → H.Adj x y → p = y := by
    intro y hy hxy
    have hp : ∃ y ∈ S, H.Adj x y := ⟨y, hy, hxy⟩
    simp only [p, hp, dite_true]
    exact hx _ _ hp.choose_spec.1 hy hp.choose_spec.2 hxy
  by_cases hax : a = x
  · subst hax
    have hbx : b ≠ a := hab.ne.symm
    simp only [f, hbx, ite_false, ite_true]
    rw [hpn b hb hab]
  by_cases hbx : b = x
  · subst hbx
    simp only [f, hax, ite_false, ite_true]
    rw [hpn a ha hab.symm]
  simp only [f, hax, hbx, ite_false]
  apply Adj.reachable
  rw [deleteEdges_adj_iff]
  exact ⟨⟨hab, ⟨ha, hax⟩, ⟨hb, hbx⟩⟩, hne⟩
end ErdosPosa
