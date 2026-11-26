-- Prove2me | solution 1 for DenseTriangleFree.patZ_01
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:52:11.082254+00:00
-- url     : https://prove2.me/submissions/45997244-99cd-42d8-ac0c-0ec4945464ba

module
public import Mathlib
public import Definitions.Def_JinLib_Pairs
public import Definitions.Def_JinLib_Maximal
public import Definitions.Def_JinLib_Patterns
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
omit hmax
namespace DenseTriangleFree
theorem _root_.solution (hbest : ∀ (b : V) (W : Fin 5 → V), IsPair G b W → (sSet G b W).card ≤ 2)
    (x0 x1 x2 x3 x4 x5 x6 x7 : V) (h_1_2 : G.Adj x1 x2) (h_2_3 : G.Adj x2 x3)
    (h_3_4 : G.Adj x3 x4) (h_4_5 : G.Adj x4 x5) (h_5_1 : G.Adj x5 x1) (n_0_4 : ¬ G.Adj x0 x4)
    (h_0_6 : G.Adj x0 x6) (h_5_6 : G.Adj x5 x6) (h_2_6 : G.Adj x2 x6) (h_0_7 : G.Adj x0 x7)
    (h_1_7 : G.Adj x1 x7) (h_3_7 : G.Adj x3 x7)
    (f2 : ∀ t, G.Adj x0 t → G.Adj x2 t → G.Adj x4 t → False)
    (f3 : ∀ t, G.Adj x0 t → G.Adj x3 t → G.Adj x5 t → False)
    (f4 : ∀ t, G.Adj x0 t → G.Adj x4 t → G.Adj x1 t → False) :
    False := by
  obtain ⟨J, hJ, x8, hx⟩ := heavy_step G h3 hδ
    (fun i => [x0, x1, x2, x3, x4, x5, x6, x7].getD i x0)
    [1, 0, 0, 1, 1, 1, 1, 1]
    [(0, 6), (0, 7), (1, 2), (1, 7), (2, 3), (2, 6), (3, 4), (3, 7), (4, 5), (5, 1), (5, 6)]
    [[0, 2, 4], [0, 3, 5], [0, 4, 1]]
    [[4, 6, 7]]
    (by
      simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
        implies_true, and_true]
      exact ⟨h_0_6, h_0_7, h_1_2, h_1_7, h_2_3, h_2_6, h_3_4, h_3_7, h_4_5, h_5_1, h_5_6⟩)
    (by
      intro F hF y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
      rcases hF with rfl | rfl | rfl
      · exact f2 y (hy 0 (by simp)) (hy 2 (by simp)) (hy 4 (by simp))
      · exact f3 y (hy 0 (by simp)) (hy 3 (by simp)) (hy 5 (by simp))
      · exact f4 y (hy 0 (by simp)) (hy 4 (by simp)) (hy 1 (by simp)))
    (by decide) (by decide +kernel)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hJ
  subst hJ
  have h_4_8 : G.Adj x4 x8 := hx 4 (by simp)
  have h_6_8 : G.Adj x6 x8 := hx 6 (by simp)
  have h_7_8 : G.Adj x7 x8 := hx 7 (by simp)
  exact pair_contra G hbest x4 x0 x6 x2 x1 x7
    h_0_6 h_2_6.symm h_1_2.symm h_1_7 h_0_7.symm
    (fun h : G.Adj x4 x0 => n_0_4 h.symm)
    (fun h : G.Adj x4 x6 => triangle_of_cliqueFree' h3 h_4_5 h_5_6 h.symm)
    (fun h : G.Adj x4 x2 => triangle_of_cliqueFree' h3 h_2_3 h_3_4 h)
    (fun h : G.Adj x4 x1 => triangle_of_cliqueFree' h3 h_5_1.symm h_4_5.symm h)
    (fun h : G.Adj x4 x7 => triangle_of_cliqueFree' h3 h_3_4.symm h_3_7 h.symm)
    {0, 2, 3} (by decide) (by
      intro i hi
      fin_cases hi
      · exact ⟨x8, h_4_8, h_7_8, h_6_8⟩
      · exact ⟨x5, h_4_5, h_5_6.symm, h_5_1.symm⟩
      · exact ⟨x3, h_3_4.symm, h_2_3, h_3_7.symm⟩)
end DenseTriangleFree
