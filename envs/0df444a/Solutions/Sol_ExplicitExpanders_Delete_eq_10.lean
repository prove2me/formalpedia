-- Prove2me | solution 1 for ExplicitExpanders.Delete.eq_10
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T23:19:34.459233+00:00
-- url     : https://prove2.me/submissions/2e3242a1-2431-45f4-9ae7-4c72fffaf5df

import Mathlib
import Definitions.Def_ExplicitExpanders_Delete_IsNDLambda
import Definitions.Def_ExplicitExpanders_Delete_Neighbourhoods
import Definitions.Def_ExplicitExpanders_Delete_DeleteAndMatch

set_option autoImplicit false

open Matrix Finset in

theorem a15c670b_generic {W : Type*} [Fintype W] [DecidableEq W] (G : SimpleGraph W)
    [DecidableRel G.Adj] [∀ v, Fintype (G.neighborSet v)] (f : W → ℝ) :
    |f ⬝ᵥ (G.adjMatrix ℝ *ᵥ f)| ≤ ∑ x, (G.degree x : ℝ) * f x ^ 2 := by
  have hdeg : ∀ x, (G.degree x : ℝ) = ∑ y, if G.Adj x y then (1 : ℝ) else 0 := by
    intro x
    classical
    rw [Finset.sum_boole]
    have : G.degree x = (Finset.univ.filter (G.Adj x)).card := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      congr 1
      ext y; simp
    rw [this]
  have hA : f ⬝ᵥ (G.adjMatrix ℝ *ᵥ f) = ∑ x, ∑ y, if G.Adj x y then f x * f y else 0 := by
    simp only [dotProduct, mulVec, SimpleGraph.adjMatrix_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    split_ifs <;> ring
  have hsym : (∑ x, ∑ y, if G.Adj x y then f y ^ 2 else 0) =
      ∑ x, ∑ y, if G.Adj x y then f x ^ 2 else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    simp only [G.adj_comm]
  have hR : ∑ x, (G.degree x : ℝ) * f x ^ 2 = ∑ x, ∑ y, if G.Adj x y then f x ^ 2 else 0 := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hdeg, Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ => ?_
    split_ifs <;> ring
  rw [hA, hR]
  calc |∑ x, ∑ y, if G.Adj x y then f x * f y else 0|
      ≤ ∑ x, ∑ y, |if G.Adj x y then f x * f y else 0| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        exact Finset.sum_le_sum fun x _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, ∑ y, ((if G.Adj x y then f x ^ 2 else 0) + (if G.Adj x y then f y ^ 2 else 0)) / 2 := by
        refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
        split_ifs
        · rw [abs_le]; constructor <;> nlinarith [sq_nonneg (f x + f y), sq_nonneg (f x - f y)]
        · simp
    _ = ∑ x, ∑ y, if G.Adj x y then f x ^ 2 else 0 := by
        simp only [← Finset.sum_div, Finset.sum_add_distrib, hsym]
        ring

open Matrix ExplicitExpanders.Delete Classical in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (m : V → V) (hm : IsMatchingOn (nbrSet H U) m) (f : Kept U → ℝ) :
    |f ⬝ᵥ ((matchGraph H U m).adjMatrix ℝ *ᵥ f)| ≤
      ∑ x, ((matchGraph H U m).degree x : ℝ) * f x ^ 2 := by
  convert a15c670b_generic (matchGraph H U m) f

