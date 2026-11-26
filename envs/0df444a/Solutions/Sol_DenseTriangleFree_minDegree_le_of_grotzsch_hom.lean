-- Prove2me | solution 1 for DenseTriangleFree.minDegree_le_of_grotzsch_hom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:49:28.100704+00:00
-- url     : https://prove2.me/submissions/d21c8344-72c0-40df-a654-2209e5c742c2

module
public import Mathlib
public import Definitions.Def_JinLib_Grotzsch
public import Theorems.Thm_DenseTriangleFree_grotzsch_indep_weight
public import Theorems.Thm_DenseTriangleFree_grotzschWt_sum
public import Theorems.Thm_DenseTriangleFree_triangle_of_cliqueFree

set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
namespace DenseTriangleFree
theorem _root_.solution {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (h3 : G.CliqueFree 3) (f : grotzsch →g G) :
    29 * G.minDegree ≤ 10 * Fintype.card V := by
  classical
  have key : ∀ y : V, ∑ x, (if G.Adj (f x) y then grotzschWt x else 0) ≤ 10 := by
    intro y
    apply grotzsch_indep_weight
    intro i j hij hi hj
    exact triangle_of_cliqueFree h3 (f.map_rel hij) hj hi
  calc 29 * G.minDegree = ∑ x, grotzschWt x * G.minDegree := by
        rw [← Finset.sum_mul, grotzschWt_sum]
    _ ≤ ∑ x, grotzschWt x * G.degree (f x) := by
        gcongr with x
        exact G.minDegree_le_degree _
    _ = ∑ x, ∑ y, (if G.Adj (f x) y then grotzschWt x else 0) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← G.card_neighborFinset_eq_degree, G.neighborFinset_eq_filter, Finset.card_filter,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        split_ifs <;> simp
    _ = ∑ y, ∑ x, (if G.Adj (f x) y then grotzschWt x else 0) := Finset.sum_comm
    _ ≤ ∑ _y : V, 10 := Finset.sum_le_sum fun y _ => key y
    _ = 10 * Fintype.card V := by simp [mul_comm]
end DenseTriangleFree
