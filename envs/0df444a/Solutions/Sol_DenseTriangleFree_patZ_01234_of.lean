-- Prove2me | solution 1 for DenseTriangleFree.patZ_01234_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:53:56.842951+00:00
-- url     : https://prove2.me/submissions/3e40a8e1-0953-44ec-8594-30d85935f285

module
public import Mathlib
public import Definitions.Def_JinLib_Pairs
public import Definitions.Def_JinLib_Maximal
public import Definitions.Def_JinLib_Patterns
public import Theorems.Thm_DenseTriangleFree_patZ_01234
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
omit hmax
namespace DenseTriangleFree
theorem _root_.solution
    (a : V) (U : Fin 5 → V) (hp : IsPair G a U)
    (hS : sSet G a U = ({0, 1, 2, 3, 4} : Finset (Fin 5))) :
    False := by
  obtain ⟨hU, hn⟩ := hp
  have hin : ∀ j, j ∈ ({0, 1, 2, 3, 4} : Finset (Fin 5)) →
      ∃ t, G.Adj a t ∧ G.Adj (U (j - 1)) t ∧ G.Adj (U (j + 1)) t :=
    fun j hj => (mem_sSet G).1 (by rw [hS]; exact hj)
  obtain ⟨v0, hv0a, hv0b, hv0c⟩ := hin 0 (by decide)
  obtain ⟨v1, hv1a, hv1b, hv1c⟩ := hin 1 (by decide)
  obtain ⟨v2, hv2a, hv2b, hv2c⟩ := hin 2 (by decide)
  obtain ⟨v3, hv3a, hv3b, hv3c⟩ := hin 3 (by decide)
  obtain ⟨v4, hv4a, hv4b, hv4c⟩ := hin 4 (by decide)
  exact patZ_01234 G h3 hδ a (U 0) (U 1) (U 2) (U 3) (U 4) v0 v1 v2 v3 v4 (hU 0) (hU 1) (hU 2)
    (hU 3) (hU 4) hv0a hv0b hv0c hv1a hv1b hv1c hv2a hv2b hv2c hv3a hv3b hv3c hv4a hv4b hv4c
end DenseTriangleFree
