-- Prove2me | solution 1 for DenseTriangleFree.patZ_none_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:54:58.699157+00:00
-- url     : https://prove2.me/submissions/2695bcfc-164d-4eba-9492-a6ac249f31c1

module
public import Mathlib
public import Definitions.Def_JinLib_Pairs
public import Definitions.Def_JinLib_Maximal
public import Definitions.Def_JinLib_Patterns
public import Theorems.Thm_DenseTriangleFree_patZ_none
public import Theorems.Thm_DenseTriangleFree_mem_sSet


set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
open SimpleGraph
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (h3 : G.CliqueFree 3) (hmax : Maximal (fun H : SimpleGraph V => H.CliqueFree 3) G)
  (hδ : 10 * Fintype.card V < 29 * G.minDegree)
include h3 hmax hδ
namespace DenseTriangleFree
theorem _root_.solution
    (hbest : ∀ (b : V) (W : Fin 5 → V), IsPair G b W → (sSet G b W).card ≤ 0)
    (a : V) (U : Fin 5 → V) (hp : IsPair G a U)
    (hS : sSet G a U = (∅ : Finset (Fin 5))) :
    False := by
  obtain ⟨hU, hn⟩ := hp
  have hout : ∀ j, j ∉ (∅ : Finset (Fin 5)) →
      ∀ t, G.Adj a t → G.Adj (U (j - 1)) t → G.Adj (U (j + 1)) t → False :=
    fun j hj t h1 h2 h3 => hj (by rw [← hS]; exact (mem_sSet G).2 ⟨t, h1, h2, h3⟩)
  exact patZ_none G h3 hmax hδ hbest a (U 0) (U 1) (U 2) (U 3) (U 4) (hU 0) (hU 1) (hU 2) (hU 3)
    (hU 4) (hn 0) (hn 1) (hn 2) (hout 0 (by decide)) (hout 1 (by decide)) (hout 2 (by decide))
    (hout 3 (by decide)) (hout 4 (by decide))
end DenseTriangleFree
