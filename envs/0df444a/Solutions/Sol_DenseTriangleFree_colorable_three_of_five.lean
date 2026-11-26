-- Prove2me | solution 1 for DenseTriangleFree.colorable_three_of_five
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:59:02.799911+00:00
-- url     : https://prove2.me/submissions/da76f737-0336-4a77-8c41-18d480c5a683

module
public import Mathlib
public import Definitions.Def_JinLib_KeyLemma
public import Definitions.Def_JinLib_Bipartite
public import Theorems.Thm_DenseTriangleFree_succ_mod_cases
public import Theorems.Thm_DenseTriangleFree_no_odd_walk
public import Theorems.Thm_P2M_DenseTriangleFree_triangle_of_cliqueFree__32533396f53c


set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}
namespace DenseTriangleFree
theorem _root_.solution (h3 : G.CliqueFree 3)
    (hcn : ∀ u v, u ≠ v → ¬ G.Adj u v → ∃ w, G.Adj u w ∧ G.Adj v w)
    (hZ : ∀ (a : V) (U : Fin 5 → V), (∀ i, G.Adj (U i) (U (i + 1))) → ∃ i, G.Adj a (U i)) :
    G.Colorable 3 := by
  classical
  rcases isEmpty_or_nonempty V with hV | ⟨⟨a⟩⟩
  · exact ⟨Coloring.mk (fun v => isEmptyElim v) (fun {v} => isEmptyElim v)⟩
  have h2 : (G.induce {v | ¬ G.Adj a v}).Colorable 2 := by
    rw [two_colorable_iff_forall_loop_even]
    intro u w
    rw [← Nat.not_odd_iff_even]
    intro hodd
    have hm : 0 < w.length := hodd.pos
    refine no_odd_walk h3 hcn hZ a w.length (fun k => (w.getVert (k % w.length)).val)
      (fun i => by simp only [Nat.add_mod_right]) (fun i => ?_)
      (fun i => (w.getVert (i % w.length)).prop) hodd
    have key : ∀ j < w.length, G.Adj (w.getVert j).val (w.getVert (j + 1)).val :=
      fun j hj => w.adj_getVert_succ hj
    rcases succ_mod_cases i w.length hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h2]
      exact key (i % w.length) (Nat.mod_lt i hm)
    · rw [h2]
      have := key (i % w.length) (Nat.mod_lt i hm)
      rw [h1, Walk.getVert_length] at this
      rwa [Walk.getVert_zero]
  obtain ⟨col⟩ := h2
  refine ⟨Coloring.mk (fun v => if h : G.Adj a v then 2 else (col ⟨v, h⟩).castSucc) ?_⟩
  intro u v huv
  by_cases hu : G.Adj a u <;> by_cases hv : G.Adj a v <;> simp only [hu, hv, dite_true, dite_false]
  · exact fun _ => triangle_of_cliqueFree' h3 hu huv hv.symm
  · generalize col ⟨v, hv⟩ = x
    revert x
    decide
  · generalize col ⟨u, hu⟩ = x
    revert x
    decide
  · intro h
    exact col.valid (show (G.induce {v | ¬ G.Adj a v}).Adj ⟨u, hu⟩ ⟨v, hv⟩ from huv)
      (Fin.castSucc_injective _ h)
end DenseTriangleFree
