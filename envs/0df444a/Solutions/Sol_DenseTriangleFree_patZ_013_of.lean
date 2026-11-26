-- Prove2me | solution 1 for DenseTriangleFree.patZ_013_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:54:08.247635+00:00
-- url     : https://prove2.me/submissions/32c5241e-f592-4a83-ad9f-4f56f7026f88

module
public import Mathlib
public import Definitions.Def_JinLib_Pairs
public import Definitions.Def_JinLib_Maximal
public import Definitions.Def_JinLib_Patterns
public import Theorems.Thm_DenseTriangleFree_patZ_013
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
    (hbest : ∀ (b : V) (W : Fin 5 → V), IsPair G b W → (sSet G b W).card ≤ 3)
    (a : V) (U : Fin 5 → V) (hp : IsPair G a U)
    (hS : sSet G a U = ({0, 1, 3} : Finset (Fin 5))) :
    False := by
  obtain ⟨hU, hn⟩ := hp
  have hin : ∀ j, j ∈ ({0, 1, 3} : Finset (Fin 5)) →
      ∃ t, G.Adj a t ∧ G.Adj (U (j - 1)) t ∧ G.Adj (U (j + 1)) t :=
    fun j hj => (mem_sSet G).1 (by rw [hS]; exact hj)
  have hout : ∀ j, j ∉ ({0, 1, 3} : Finset (Fin 5)) →
      ∀ t, G.Adj a t → G.Adj (U (j - 1)) t → G.Adj (U (j + 1)) t → False :=
    fun j hj t h1 h2 h3 => hj (by rw [← hS]; exact (mem_sSet G).2 ⟨t, h1, h2, h3⟩)
  obtain ⟨v0, hv0a, hv0b, hv0c⟩ := hin 0 (by decide)
  obtain ⟨v1, hv1a, hv1b, hv1c⟩ := hin 1 (by decide)
  obtain ⟨v3, hv3a, hv3b, hv3c⟩ := hin 3 (by decide)
  exact patZ_013 G h3 hmax hδ hbest a (U 0) (U 1) (U 2) (U 3) (U 4) v0 v1 v3 (hU 0) (hU 1)
    (hU 2) (hU 3) (hU 4) (hn 2) (hn 3) hv0a hv0b hv0c hv1a hv1b hv1c hv3a hv3b hv3c
    (hout 2 (by decide)) (hout 4 (by decide))
end DenseTriangleFree
