-- Prove2me | solution 1 for GalvinMultigraph.Gadget.terminal_agreement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:52:14.201563+00:00
-- url     : https://prove2.me/submissions/0ebb2e24-a1e1-4da3-8764-f8bee83eb28d

module
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Definitions.Def_GalvinMultigraph_Gadget
public import Theorems.Thm_GalvinMultigraph_Gadget_lists_aEdge
public import Theorems.Thm_GalvinMultigraph_Gadget_lists_bEdge
public import Theorems.Thm_GalvinMultigraph_Gadget_lists_innerEdge
public import Theorems.Thm_GalvinMultigraph_Gadget_lists_rowEdge
public import Theorems.Thm_GalvinMultigraph_Gadget_edge_eq_of_color_eq
public import Theorems.Thm_GalvinMultigraph_Gadget_rowColor_injective
public import Theorems.Thm_GalvinMultigraph_Gadget_columnColor_injective
attribute [local simp] GalvinMultigraph.Gadget.lists_aEdge
attribute [local simp] GalvinMultigraph.Gadget.lists_bEdge
attribute [local simp] GalvinMultigraph.Gadget.lists_innerEdge
attribute [local simp] GalvinMultigraph.Gadget.lists_rowEdge

set_option autoImplicit true
@[expose] public section
public section
open GalvinMultigraph GalvinMultigraph.Gadget
open Finset SimpleGraph
variable {A B E Color : Type*} {k : ℕ} [NeZero k]
namespace GalvinMultigraph.Gadget
theorem _root_.solution (a : E → A) (b : E → B) (P : E → Finset Color)
    (col : (graph (k := k) a b).lineGraph.Coloring Color)
    (hcol : ∀ f, col f ∈ lists a b P f) (e : E) (hP : (P e).card = k) :
    col (aEdge a b e) = col (bEdge a b e) := by
  classical
  have hm (i j : Fin k) : col (rowEdge a b e i j) ∈ P e := by
    simpa using hcol (rowEdge a b e i j)
  have hrow (i : Fin k) : ∃ j, col (rowEdge a b e i j) = col (aEdge a b e) := by
    let f : Fin k → {c // c ∈ P e} := fun j => ⟨col (rowEdge a b e i j), hm i j⟩
    have hf : Function.Injective f := by
      intro j j' h
      exact rowColor_injective a b col e i (congrArg Subtype.val h)
    have hcard : Fintype.card (Fin k) = Fintype.card {c // c ∈ P e} := by simp [hP]
    have hsurj := (Finite.injective_iff_surjective_of_equiv (Fintype.equivOfCardEq hcard)).mp hf
    have ha : col (aEdge a b e) ∈ P e := by simpa using hcol (aEdge a b e)
    obtain ⟨j, hj⟩ := hsurj ⟨col (aEdge a b e), ha⟩
    exact ⟨j, congrArg Subtype.val hj⟩
  choose g hg using hrow
  by_contra hne
  have hg0 (i : Fin k) : g i ≠ 0 := by
    intro hzero
    have h := hg i
    rw [hzero] at h
    by_cases hi : i = 0
    · subst i
      exact hne (by simpa [rowEdge] using h.symm)
    · have hbad : rowEdge a b e i 0 ≠ aEdge a b e := by
        intro heq
        have heq' := congrArg Subtype.val heq
        simp [rowEdge, hi, innerEdge, aEdge] at heq'
      apply hbad
      apply edge_eq_of_color_eq col (v := Sum.inr (Sum.inr (e, 0))) _ _ h
      · simp [rowEdge, hi, innerEdge]
      · simp [aEdge]
  have hginj : Function.Injective g := by
    intro i i' h
    apply columnColor_injective a b col e (g i) (hg0 i)
    calc col (rowEdge a b e i (g i)) = col (aEdge a b e) := hg i
      _ = col (rowEdge a b e i' (g i)) := by rw [h, hg i']
  obtain ⟨i, hi⟩ := Finite.surjective_of_injective hginj 0
  exact hg0 i hi
end GalvinMultigraph.Gadget
