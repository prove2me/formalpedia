-- Prove2me | solution 1 for DenseTriangleFree.patZ_02
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:52:12.04618+00:00
-- url     : https://prove2.me/submissions/618eab18-c70b-42df-94a5-aac34a6599b0

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
theorem _root_.solution (hbest : ∀ (b : V) (W : Fin 5 → V), IsPair G b W → (sSet G b W).card ≤ 2)
    (x0 x1 x2 x3 x4 x5 x6 x7 : V) (h_1_2 : G.Adj x1 x2) (h_2_3 : G.Adj x2 x3)
    (h_3_4 : G.Adj x3 x4) (h_4_5 : G.Adj x4 x5) (h_5_1 : G.Adj x5 x1) (n_0_1 : ¬ G.Adj x0 x1)
    (n_0_2 : ¬ G.Adj x0 x2) (h_0_6 : G.Adj x0 x6) (h_5_6 : G.Adj x5 x6) (h_2_6 : G.Adj x2 x6)
    (h_0_7 : G.Adj x0 x7) (h_2_7 : G.Adj x2 x7) (h_4_7 : G.Adj x4 x7)
    (f1 : ∀ t, G.Adj x0 t → G.Adj x1 t → G.Adj x3 t → False)
    (f3 : ∀ t, G.Adj x0 t → G.Adj x3 t → G.Adj x5 t → False)
    (f4 : ∀ t, G.Adj x0 t → G.Adj x4 t → G.Adj x1 t → False) :
    False := by
  obtain ⟨x8, h_0_8, h_1_8⟩ := exists_common_neighbor_of_maximal hmax
    (fun h : x0 = x1 => (fun h : G.Adj x2 x0 => n_0_2 h.symm) (by rw [h]; exact h_1_2.symm))
    n_0_1
  obtain ⟨J, hJ, x9, hx⟩ := heavy_step G h3 hδ
    (fun i => [x0, x1, x2, x3, x4, x5, x6, x7, x8].getD i x0)
    [1, 1, 0, 0, 1, 1, 0, 1, 1]
    [(0, 6), (0, 7), (0, 8), (1, 2), (1, 8), (2, 3), (2, 6), (2, 7), (3, 4), (4, 5), (4, 7),
     (5, 1), (5, 6)]
    [[0, 1, 3], [0, 3, 5], [0, 4, 1]]
    [[5, 7, 8]]
    (by
      simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
        implies_true, and_true]
      exact ⟨h_0_6, h_0_7, h_0_8, h_1_2, h_1_8, h_2_3, h_2_6, h_2_7, h_3_4, h_4_5, h_4_7, h_5_1,
             h_5_6⟩)
    (by
      intro F hF y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
      rcases hF with rfl | rfl | rfl
      · exact f1 y (hy 0 (by simp)) (hy 1 (by simp)) (hy 3 (by simp))
      · exact f3 y (hy 0 (by simp)) (hy 3 (by simp)) (hy 5 (by simp))
      · exact f4 y (hy 0 (by simp)) (hy 4 (by simp)) (hy 1 (by simp)))
    (by decide) (by decide +kernel)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hJ
  subst hJ
  have h_5_9 : G.Adj x5 x9 := hx 5 (by simp)
  have h_7_9 : G.Adj x7 x9 := hx 7 (by simp)
  have h_8_9 : G.Adj x8 x9 := hx 8 (by simp)
  exact pair_contra G hbest x8 x2 x6 x5 x4 x7
    h_2_6 h_5_6.symm h_4_5.symm h_4_7 h_2_7.symm
    (fun h : G.Adj x8 x2 => triangle_of_cliqueFree' h3 h_1_2.symm h_1_8 h)
    (fun h : G.Adj x8 x6 => triangle_of_cliqueFree' h3 h_0_6.symm h_0_8 h)
    (fun h : G.Adj x8 x5 => triangle_of_cliqueFree' h3 h_5_1 h_1_8 h)
    (fun h : G.Adj x8 x4 => f4 x8 h_0_8 h.symm h_1_8)
    (fun h : G.Adj x8 x7 => triangle_of_cliqueFree' h3 h_0_7.symm h_0_8 h)
    {0, 1, 3} (by decide) (by
      intro i hi
      fin_cases hi
      · exact ⟨x0, h_0_8.symm, h_0_7.symm, h_0_6.symm⟩
      · exact ⟨x1, h_1_8.symm, h_1_2.symm, h_5_1⟩
      · exact ⟨x9, h_8_9, h_5_9, h_7_9⟩)
end DenseTriangleFree
