-- Prove2me | solution 1 for DenseTriangleFree.jin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:03:40.907429+00:00
-- url     : https://prove2.me/submissions/57f37cd2-8d29-46b2-b5db-3ee0b619aea2

module
public import Mathlib
public import Definitions.Def_JinLib_Blowup
public import Definitions.Def_JinLib_Maximal
public import Definitions.Def_JinLib_Bipartite
public import Definitions.Def_JinLib_Jin
public import Theorems.Thm_DenseTriangleFree_colorable_of_maximal
public import Theorems.Thm_DenseTriangleFree_jin_of_maximal


set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
namespace DenseTriangleFree
theorem _root_.solution {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h3 : G.CliqueFree 3) (hδ : 10 * Fintype.card V < 29 * G.minDegree) : G.Colorable 3 := by
  -- Step 0 (proved): reduce to maximal triangle-free graphs.
  refine jin_of_maximal ?_ G h3 hδ
  intro G' _ hmax hδ'
  -- Step 1 (`key_lemma`): every vertex of `G'` is adjacent to some vertex of every closed walk of
  -- length 5. The extremal case of its proof is a homomorphic image of the Grötzsch graph, excluded
  -- by the same weighting as in `minDegree_le_of_grotzsch_hom`.
  -- Step 2 (`colorable_of_maximal`): hence the non-neighbourhood of any vertex `a` has no odd
  -- closed walk, so it is bipartite, and the neighbourhood of `a` receives the third colour.
  exact colorable_of_maximal hmax hδ'
end DenseTriangleFree
