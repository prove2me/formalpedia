-- Prove2me | solution 1 for DenseTriangleFree.patZ_013
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:52:06.73464+00:00
-- url     : https://prove2.me/submissions/5ee9f25a-e898-4838-b5b2-8576129208e1

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
theorem _root_.solution (hbest : ∀ (b : V) (W : Fin 5 → V), IsPair G b W → (sSet G b W).card ≤ 3)
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 : V) (h_1_2 : G.Adj x1 x2) (h_2_3 : G.Adj x2 x3)
    (h_3_4 : G.Adj x3 x4) (h_4_5 : G.Adj x4 x5) (h_5_1 : G.Adj x5 x1) (n_0_3 : ¬ G.Adj x0 x3)
    (n_0_4 : ¬ G.Adj x0 x4) (h_0_6 : G.Adj x0 x6) (h_5_6 : G.Adj x5 x6) (h_2_6 : G.Adj x2 x6)
    (h_0_7 : G.Adj x0 x7) (h_1_7 : G.Adj x1 x7) (h_3_7 : G.Adj x3 x7) (h_0_8 : G.Adj x0 x8)
    (h_3_8 : G.Adj x3 x8) (h_5_8 : G.Adj x5 x8)
    (f2 : ∀ t, G.Adj x0 t → G.Adj x2 t → G.Adj x4 t → False)
    (f4 : ∀ t, G.Adj x0 t → G.Adj x4 t → G.Adj x1 t → False) :
    False := by
  obtain ⟨x9, h_0_9, h_4_9⟩ := exists_common_neighbor_of_maximal hmax
    (fun h : x0 = x4 => (fun h : G.Adj x3 x0 => n_0_3 h.symm) (by rw [h]; exact h_3_4))
    n_0_4
  obtain ⟨J, hJ, x10, hx⟩ := heavy_step G h3 hδ
    (fun i => [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9].getD i x0)
    [1, 0, 1, 1, 1, 0, 1, 0, 0, 1]
    [(0, 6), (0, 7), (0, 8), (0, 9), (1, 2), (1, 7), (2, 3), (2, 6), (3, 4), (3, 7), (3, 8),
     (4, 5), (4, 9), (5, 1), (5, 6), (5, 8)]
    [[0, 2, 4], [0, 4, 1]]
    [[3, 6, 9]]
    (by
      simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
        implies_true, and_true]
      exact ⟨h_0_6, h_0_7, h_0_8, h_0_9, h_1_2, h_1_7, h_2_3, h_2_6, h_3_4, h_3_7, h_3_8, h_4_5,
             h_4_9, h_5_1, h_5_6, h_5_8⟩)
    (by
      intro F hF y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
      rcases hF with rfl | rfl
      · exact f2 y (hy 0 (by simp)) (hy 2 (by simp)) (hy 4 (by simp))
      · exact f4 y (hy 0 (by simp)) (hy 4 (by simp)) (hy 1 (by simp)))
    (by decide) (by decide +kernel)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hJ
  subst hJ
  have h_3_10 : G.Adj x3 x10 := hx 3 (by simp)
  have h_6_10 : G.Adj x6 x10 := hx 6 (by simp)
  have h_9_10 : G.Adj x9 x10 := hx 9 (by simp)
  obtain ⟨J, hJ, x11, hx⟩ := heavy_step G h3 hδ
    (fun i => [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10].getD i x0)
    [1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0]
    [(0, 6), (0, 7), (0, 8), (0, 9), (1, 2), (1, 7), (2, 3), (2, 6), (3, 4), (3, 7), (3, 8),
     (3, 10), (4, 5), (4, 9), (5, 1), (5, 6), (5, 8), (6, 10), (9, 10)]
    [[0, 2, 4], [0, 4, 1]]
    [[5, 7, 9]]
    (by
      simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
        implies_true, and_true]
      exact ⟨h_0_6, h_0_7, h_0_8, h_0_9, h_1_2, h_1_7, h_2_3, h_2_6, h_3_4, h_3_7, h_3_8,
             h_3_10, h_4_5, h_4_9, h_5_1, h_5_6, h_5_8, h_6_10, h_9_10⟩)
    (by
      intro F hF y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
      rcases hF with rfl | rfl
      · exact f2 y (hy 0 (by simp)) (hy 2 (by simp)) (hy 4 (by simp))
      · exact f4 y (hy 0 (by simp)) (hy 4 (by simp)) (hy 1 (by simp)))
    (by decide) (by decide +kernel)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hJ
  subst hJ
  have h_5_11 : G.Adj x5 x11 := hx 5 (by simp)
  have h_7_11 : G.Adj x7 x11 := hx 7 (by simp)
  have h_9_11 : G.Adj x9 x11 := hx 9 (by simp)
  exact pair_contra G hbest x3 x0 x6 x5 x11 x9
    h_0_6 h_5_6.symm h_5_11 h_9_11.symm h_0_9.symm
    (fun h : G.Adj x3 x0 => n_0_3 h.symm)
    (fun h : G.Adj x3 x6 => triangle_of_cliqueFree' h3 h_2_3.symm h_2_6 h.symm)
    (fun h : G.Adj x3 x5 => triangle_of_cliqueFree' h3 h_3_4 h_4_5 h.symm)
    (fun h : G.Adj x3 x11 => triangle_of_cliqueFree' h3 h_3_7 h_7_11 h.symm)
    (fun h : G.Adj x3 x9 => triangle_of_cliqueFree' h3 h_3_4 h_4_9 h.symm)
    {0, 1, 3, 4} (by decide) (by
      intro i hi
      fin_cases hi
      · exact ⟨x10, h_3_10, h_9_10, h_6_10⟩
      · exact ⟨x8, h_3_8, h_0_8, h_5_8⟩
      · exact ⟨x4, h_3_4, h_4_5.symm, h_4_9.symm⟩
      · exact ⟨x7, h_3_7, h_7_11.symm, h_0_7⟩)
end DenseTriangleFree
