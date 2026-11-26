-- Prove2me | solution 1 for DenseTriangleFree.heavy_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:50:04.142792+00:00
-- url     : https://prove2.me/submissions/6d34ded4-7f2b-41b6-88ab-364143bbb11c

module
public import Mathlib
public import Definitions.Def_JinLib_Grotzsch
public import Definitions.Def_JinLib_Heavy
public import Theorems.Thm_DenseTriangleFree_enumIndep_sound
public import Theorems.Thm_DenseTriangleFree_heavyTest_perm
public import Theorems.Thm_DenseTriangleFree_exists_heavy_vertex
public import Theorems.Thm_P2M_DenseTriangleFree_triangle_of_cliqueFree__32533396f53c
public import Theorems.Thm_DenseTriangleFree_list_sum_eq_range
public import Theorems.Thm_DenseTriangleFree_wsumL_filter

set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
open SimpleGraph
namespace DenseTriangleFree
theorem _root_.solution {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h3 : G.CliqueFree 3) (hδ : 10 * Fintype.card V < 29 * G.minDegree)
    (f : ℕ → V) (ws : List ℕ) (edges : List (ℕ × ℕ)) (Fb Js : List (List ℕ))
    (hE : ∀ e ∈ edges, G.Adj (f e.1) (f e.2))
    (hF : ∀ F ∈ Fb, ∀ y, (∀ i ∈ F, G.Adj (f i) y) → False)
    (hpos : 0 < ws.sum)
    (hc : heavyCheck ws edges Fb Js = true) :
    ∃ J ∈ Js, ∃ y, ∀ i ∈ J, G.Adj (f i) y := by
  classical
  have hpos' : 0 < ∑ i ∈ Finset.range ws.length, ws.getD i 0 := by
    rwa [← list_sum_eq_range]
  obtain ⟨y, hy⟩ := exists_heavy_vertex G hδ f (fun i => ws.getD i 0) hpos'
  have hsound := enumIndep_sound (edgeFn edges) (heavyTest ws Fb Js) (heavyTest_perm ws Fb Js)
    (fun i => G.Adj (f i) y) (by
      intro i j hi hj
      by_contra hne
      simp only [edgeFn, Bool.not_eq_false, List.any_eq_true, Bool.or_eq_true,
        Bool.and_eq_true, beq_iff_eq] at hne
      obtain ⟨e, he, (⟨h1, h2⟩ | ⟨h1, h2⟩)⟩ := hne
      · have := hE e he
        rw [h1, h2] at this
        exact triangle_of_cliqueFree' h3 this hj hi.symm
      · have := hE e he
        rw [h1, h2] at this
        exact triangle_of_cliqueFree' h3 this hi hj.symm)
    _ [] (by simp) hc
  rw [List.append_nil] at hsound
  simp only [heavyTest, Bool.or_eq_true, List.any_eq_true, List.all_eq_true] at hsound
  rw [wsumL_filter] at hsound
  rcases hsound with (hl | ⟨F, hF', hFall⟩) | ⟨J, hJ, hJall⟩
  · rw [list_sum_eq_range] at hl
    have := Nat.le_of_ble_eq_true hl
    omega
  · exfalso
    refine hF F hF' y fun i hi => ?_
    have := hFall i hi
    simp only [List.elem_iff, List.mem_filter, decide_eq_true_eq] at this
    exact this.2
  · refine ⟨J, hJ, y, fun i hi => ?_⟩
    have := hJall i hi
    simp only [List.elem_iff, List.mem_filter, decide_eq_true_eq] at this
    exact this.2
end DenseTriangleFree
