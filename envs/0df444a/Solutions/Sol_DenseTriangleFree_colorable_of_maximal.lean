-- Prove2me | solution 1 for DenseTriangleFree.colorable_of_maximal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:01:28.174699+00:00
-- url     : https://prove2.me/submissions/d07945f9-bcaa-4a30-944a-d36f14087789

module
public import Mathlib
public import Definitions.Def_JinLib_KeyLemma
public import Definitions.Def_JinLib_Bipartite
public import Theorems.Thm_DenseTriangleFree_colorable_three_of_five
public import Theorems.Thm_DenseTriangleFree_exists_common_neighbor_of_maximal
public import Theorems.Thm_DenseTriangleFree_key_lemma


set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}
namespace DenseTriangleFree
theorem _root_.solution [Fintype V] [DecidableRel G.Adj]
    (hmax : Maximal (fun H : SimpleGraph V => H.CliqueFree 3) G)
    (hδ : 10 * Fintype.card V < 29 * G.minDegree) : G.Colorable 3 := by
  refine colorable_three_of_five hmax.prop
    (fun u v huv hn => exists_common_neighbor_of_maximal hmax huv hn) (fun a U hU => ?_)
  by_contra h
  push Not at h
  exact key_lemma G hmax.prop hmax hδ a U ⟨hU, h⟩
end DenseTriangleFree
