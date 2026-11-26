-- Prove2me | solution 1 for DenseTriangleFree.blowup_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:49:34.351399+00:00
-- url     : https://prove2.me/submissions/facead84-f51a-4172-9b4f-8f13cc07e800

module
public import Definitions.Def_JinLib_Grotzsch
public import Definitions.Def_JinLib_Blowup
public import Theorems.Thm_DenseTriangleFree_slotProj_card

set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
open SimpleGraph
namespace DenseTriangleFree
theorem _root_.solution (m : ℕ) (a : Fin (29 * m)) : (blowup m).degree a = 10 * m := by
  classical
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
  set x := blowProj m a
  have : (Finset.univ.filter fun b => (blowup m).Adj a b) =
      (Finset.univ.filter fun p : Fin 29 × Fin m => grotzsch.Adj x (slotProj p.1)).map
        finProdFinEquiv.toEmbedding := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map_equiv]
    simp [blowup, blowProj, x]
  rw [this, Finset.card_map]
  rw [show (Finset.univ.filter fun p : Fin 29 × Fin m => grotzsch.Adj x (slotProj p.1)) =
    (Finset.univ.filter fun k : Fin 29 => grotzsch.Adj x (slotProj k)) ×ˢ Finset.univ by
      ext p; simp]
  rw [Finset.card_product, slotProj_card]
  simp
end DenseTriangleFree
