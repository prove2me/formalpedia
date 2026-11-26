-- Prove2me | solution 1 for DenseTriangleFree.jin_of_maximal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:49:42.147794+00:00
-- url     : https://prove2.me/submissions/2030837d-76b4-4bfe-aa05-16212f4d6a82

module
public import Mathlib
public import Definitions.Def_JinLib_Grotzsch
public import Definitions.Def_JinLib_Maximal
public import Theorems.Thm_DenseTriangleFree_exists_maximal_cliqueFree_three_le

set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
open SimpleGraph
variable {V : Type*}
namespace DenseTriangleFree
theorem _root_.solution [Fintype V]
    (hcore : ∀ G' : SimpleGraph V, [DecidableRel G'.Adj] →
      Maximal (fun H : SimpleGraph V => H.CliqueFree 3) G' →
      10 * Fintype.card V < 29 * G'.minDegree → G'.Colorable 3)
    (G : SimpleGraph V) [DecidableRel G.Adj] (h3 : G.CliqueFree 3)
    (hδ : 10 * Fintype.card V < 29 * G.minDegree) : G.Colorable 3 := by
  classical
  obtain ⟨G', hle, hmax⟩ := exists_maximal_cliqueFree_three_le h3
  have hδ' : 10 * Fintype.card V < 29 * G'.minDegree :=
    lt_of_lt_of_le hδ (Nat.mul_le_mul_left _ (minDegree_le_minDegree hle))
  exact (hcore G' hmax hδ').mono_left hle
end DenseTriangleFree
