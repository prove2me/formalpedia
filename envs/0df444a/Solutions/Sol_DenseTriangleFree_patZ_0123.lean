-- Prove2me | solution 1 for DenseTriangleFree.patZ_0123
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:52:04.92384+00:00
-- url     : https://prove2.me/submissions/68fe031e-ed23-43a7-b39a-8aca2be94324

module
public import Mathlib
public import Definitions.Def_JinLib_Pairs
public import Definitions.Def_JinLib_Maximal
public import Definitions.Def_JinLib_Patterns
public import Theorems.Thm_DenseTriangleFree_heavy_step


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
theorem _root_.solution (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : V) (h_1_2 : G.Adj x1 x2) (h_2_3 : G.Adj x2 x3)
    (h_3_4 : G.Adj x3 x4) (h_4_5 : G.Adj x4 x5) (h_5_1 : G.Adj x5 x1) (h_0_6 : G.Adj x0 x6)
    (h_5_6 : G.Adj x5 x6) (h_2_6 : G.Adj x2 x6) (h_0_7 : G.Adj x0 x7) (h_1_7 : G.Adj x1 x7)
    (h_3_7 : G.Adj x3 x7) (h_0_8 : G.Adj x0 x8) (h_2_8 : G.Adj x2 x8) (h_4_8 : G.Adj x4 x8)
    (h_0_9 : G.Adj x0 x9) (h_3_9 : G.Adj x3 x9) (h_5_9 : G.Adj x5 x9)
    (f4 : ∀ t, G.Adj x0 t → G.Adj x4 t → G.Adj x1 t → False) :
    False := by
  obtain ⟨J, hJ, x10, hx⟩ := heavy_step G h3 hδ
    (fun i => [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9].getD i x0)
    [1, 1, 0, 0, 1, 1, 0, 1, 1, 0]
    [(0, 6), (0, 7), (0, 8), (0, 9), (1, 2), (1, 7), (2, 3), (2, 6), (2, 8), (3, 4), (3, 7),
     (3, 9), (4, 5), (4, 8), (5, 1), (5, 6), (5, 9)]
    [[0, 4, 1]]
    [[5, 7, 8]]
    (by
      simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
        implies_true, and_true]
      exact ⟨h_0_6, h_0_7, h_0_8, h_0_9, h_1_2, h_1_7, h_2_3, h_2_6, h_2_8, h_3_4, h_3_7, h_3_9,
             h_4_5, h_4_8, h_5_1, h_5_6, h_5_9⟩)
    (by
      intro F hF y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
      subst hF
      exact f4 y (hy 0 (by simp)) (hy 4 (by simp)) (hy 1 (by simp)))
    (by decide) (by decide +kernel)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hJ
  subst hJ
  have h_5_10 : G.Adj x5 x10 := hx 5 (by simp)
  have h_7_10 : G.Adj x7 x10 := hx 7 (by simp)
  have h_8_10 : G.Adj x8 x10 := hx 8 (by simp)
  obtain ⟨J, hJ, x11, hx⟩ := heavy_step G h3 hδ
    (fun i => [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10].getD i x0)
    [3, 2, 3, 3, 2, 4, 2, 3, 3, 2, 2]
    [(0, 6), (0, 7), (0, 8), (0, 9), (1, 2), (1, 7), (2, 3), (2, 6), (2, 8), (3, 4), (3, 7),
     (3, 9), (4, 5), (4, 8), (5, 1), (5, 6), (5, 9), (5, 10), (7, 10), (8, 10)]
    [[0, 4, 1]]
    []
    (by
      simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
        implies_true, and_true]
      exact ⟨h_0_6, h_0_7, h_0_8, h_0_9, h_1_2, h_1_7, h_2_3, h_2_6, h_2_8, h_3_4, h_3_7, h_3_9,
             h_4_5, h_4_8, h_5_1, h_5_6, h_5_9, h_5_10, h_7_10, h_8_10⟩)
    (by
      intro F hF y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
      subst hF
      exact f4 y (hy 0 (by simp)) (hy 4 (by simp)) (hy 1 (by simp)))
    (by decide) (by decide +kernel)
  simp at hJ
end DenseTriangleFree
