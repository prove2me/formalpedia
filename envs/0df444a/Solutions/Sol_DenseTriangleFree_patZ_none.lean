-- Prove2me | solution 1 for DenseTriangleFree.patZ_none
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:52:15.42779+00:00
-- url     : https://prove2.me/submissions/12e2017d-5433-459d-a0e6-21bc1743687f

module
public import Mathlib
public import Definitions.Def_JinLib_Pairs
public import Definitions.Def_JinLib_Maximal
public import Definitions.Def_JinLib_Patterns
public import Theorems.Thm_DenseTriangleFree_exists_common_neighbor_of_maximal
public import Theorems.Thm_DenseTriangleFree_heavy_step
public import Theorems.Thm_DenseTriangleFree_pair_contra
public import Theorems.Thm_P2M_DenseTriangleFree_triangle_of_cliqueFree__32533396f53c


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
theorem _root_.solution (hbest : ∀ (b : V) (W : Fin 5 → V), IsPair G b W → (sSet G b W).card ≤ 0)
    (x0 x1 x2 x3 x4 x5 : V) (h_1_2 : G.Adj x1 x2) (h_2_3 : G.Adj x2 x3) (h_3_4 : G.Adj x3 x4)
    (h_4_5 : G.Adj x4 x5) (h_5_1 : G.Adj x5 x1) (n_0_1 : ¬ G.Adj x0 x1) (n_0_2 : ¬ G.Adj x0 x2)
    (n_0_3 : ¬ G.Adj x0 x3) (f0 : ∀ t, G.Adj x0 t → G.Adj x5 t → G.Adj x2 t → False)
    (f1 : ∀ t, G.Adj x0 t → G.Adj x1 t → G.Adj x3 t → False)
    (f2 : ∀ t, G.Adj x0 t → G.Adj x2 t → G.Adj x4 t → False)
    (f3 : ∀ t, G.Adj x0 t → G.Adj x3 t → G.Adj x5 t → False)
    (f4 : ∀ t, G.Adj x0 t → G.Adj x4 t → G.Adj x1 t → False) :
    False := by
  obtain ⟨x6, h_0_6, h_1_6⟩ := exists_common_neighbor_of_maximal hmax
    (fun h : x0 = x1 => (fun h : G.Adj x2 x0 => n_0_2 h.symm) (by rw [h]; exact h_1_2.symm))
    n_0_1
  obtain ⟨x7, h_0_7, h_2_7⟩ := exists_common_neighbor_of_maximal hmax
    (fun h : x0 = x2 => (fun h : G.Adj x1 x0 => n_0_1 h.symm) (by rw [h]; exact h_1_2))
    n_0_2
  obtain ⟨x8, h_0_8, h_3_8⟩ := exists_common_neighbor_of_maximal hmax
    (fun h : x0 = x3 => (fun h : G.Adj x2 x0 => n_0_2 h.symm) (by rw [h]; exact h_2_3))
    n_0_3
  obtain ⟨x9, h_1_9, h_8_9⟩ := exists_common_neighbor_of_maximal hmax
    (fun h : x1 = x8 => n_0_1 (by rw [h]; exact h_0_8))
    (fun h : G.Adj x1 x8 => f1 x8 h_0_8 h h_3_8)
  obtain ⟨J, hJ, x10, hx⟩ := heavy_step G h3 hδ
    (fun i => [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9].getD i x0)
    [1, 1, 1, 0, 0, 0, 0, 1, 1, 1]
    [(0, 6), (0, 7), (0, 8), (1, 2), (1, 6), (1, 9), (2, 3), (2, 7), (3, 4), (3, 8), (4, 5),
     (5, 1), (8, 9)]
    [[0, 5, 2], [0, 1, 3], [0, 2, 4], [0, 3, 5], [0, 4, 1]]
    [[1, 7, 8], [0, 2, 9]]
    (by
      simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
        implies_true, and_true]
      exact ⟨h_0_6, h_0_7, h_0_8, h_1_2, h_1_6, h_1_9, h_2_3, h_2_7, h_3_4, h_3_8, h_4_5, h_5_1,
             h_8_9⟩)
    (by
      intro F hF y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
      rcases hF with rfl | rfl | rfl | rfl | rfl
      · exact f0 y (hy 0 (by simp)) (hy 5 (by simp)) (hy 2 (by simp))
      · exact f1 y (hy 0 (by simp)) (hy 1 (by simp)) (hy 3 (by simp))
      · exact f2 y (hy 0 (by simp)) (hy 2 (by simp)) (hy 4 (by simp))
      · exact f3 y (hy 0 (by simp)) (hy 3 (by simp)) (hy 5 (by simp))
      · exact f4 y (hy 0 (by simp)) (hy 4 (by simp)) (hy 1 (by simp)))
    (by decide) (by decide +kernel)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hJ
  rcases hJ with rfl | rfl
  · have h_1_10 : G.Adj x1 x10 := hx 1 (by simp)
    have h_7_10 : G.Adj x7 x10 := hx 7 (by simp)
    have h_8_10 : G.Adj x8 x10 := hx 8 (by simp)
    exact pair_contra G hbest x3 x0 x6 x1 x10 x7
      h_0_6 h_1_6.symm h_1_10 h_7_10.symm h_0_7.symm
      (fun h : G.Adj x3 x0 => n_0_3 h.symm)
      (fun h : G.Adj x3 x6 => f1 x6 h_0_6 h_1_6 h)
      (fun h : G.Adj x3 x1 => triangle_of_cliqueFree' h3 h_1_2 h_2_3 h)
      (fun h : G.Adj x3 x10 => triangle_of_cliqueFree' h3 h_3_8 h_8_10 h.symm)
      (fun h : G.Adj x3 x7 => triangle_of_cliqueFree' h3 h_2_3.symm h_2_7 h.symm)
      {3, 4} (by decide) (by
        intro i hi
        fin_cases hi
        · exact ⟨x2, h_2_3.symm, h_1_2, h_2_7.symm⟩
        · exact ⟨x8, h_3_8, h_8_10.symm, h_0_8⟩)
  · have h_0_10 : G.Adj x0 x10 := hx 0 (by simp)
    have h_2_10 : G.Adj x2 x10 := hx 2 (by simp)
    have h_9_10 : G.Adj x9 x10 := hx 9 (by simp)
    exact pair_contra G hbest x3 x0 x6 x1 x9 x10
      h_0_6 h_1_6.symm h_1_9 h_9_10 h_0_10.symm
      (fun h : G.Adj x3 x0 => n_0_3 h.symm)
      (fun h : G.Adj x3 x6 => f1 x6 h_0_6 h_1_6 h)
      (fun h : G.Adj x3 x1 => triangle_of_cliqueFree' h3 h_1_2 h_2_3 h)
      (fun h : G.Adj x3 x9 => triangle_of_cliqueFree' h3 h_3_8 h_8_9 h.symm)
      (fun h : G.Adj x3 x10 => triangle_of_cliqueFree' h3 h_2_3.symm h_2_10 h.symm)
      {3, 4} (by decide) (by
        intro i hi
        fin_cases hi
        · exact ⟨x2, h_2_3.symm, h_1_2, h_2_10.symm⟩
        · exact ⟨x8, h_3_8, h_8_9.symm, h_0_8⟩)
end DenseTriangleFree
