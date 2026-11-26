-- Prove2me | solution 1 for DenseTriangleFree.patZ_01234
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:52:04.087578+00:00
-- url     : https://prove2.me/submissions/1e26ca18-604c-4507-9ef9-e84c3dd55315

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
theorem _root_.solution (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : V) (h_1_2 : G.Adj x1 x2)
    (h_2_3 : G.Adj x2 x3) (h_3_4 : G.Adj x3 x4) (h_4_5 : G.Adj x4 x5) (h_5_1 : G.Adj x5 x1)
    (h_0_6 : G.Adj x0 x6) (h_5_6 : G.Adj x5 x6) (h_2_6 : G.Adj x2 x6) (h_0_7 : G.Adj x0 x7)
    (h_1_7 : G.Adj x1 x7) (h_3_7 : G.Adj x3 x7) (h_0_8 : G.Adj x0 x8) (h_2_8 : G.Adj x2 x8)
    (h_4_8 : G.Adj x4 x8) (h_0_9 : G.Adj x0 x9) (h_3_9 : G.Adj x3 x9) (h_5_9 : G.Adj x5 x9)
    (h_0_10 : G.Adj x0 x10) (h_4_10 : G.Adj x4 x10) (h_1_10 : G.Adj x1 x10) :
    False := by
  obtain ⟨J, hJ, x11, hx⟩ := heavy_step G h3 hδ
    (fun i => [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10].getD i x0)
    [4, 3, 3, 3, 3, 3, 2, 2, 2, 2, 2]
    [(0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (1, 2), (1, 7), (1, 10), (2, 3), (2, 6), (2, 8),
     (3, 4), (3, 7), (3, 9), (4, 5), (4, 8), (4, 10), (5, 1), (5, 6), (5, 9)]
    []
    []
    (by
      simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
        implies_true, and_true]
      exact ⟨h_0_6, h_0_7, h_0_8, h_0_9, h_0_10, h_1_2, h_1_7, h_1_10, h_2_3, h_2_6, h_2_8,
             h_3_4, h_3_7, h_3_9, h_4_5, h_4_8, h_4_10, h_5_1, h_5_6, h_5_9⟩)
    (by intro F hF; simp at hF)
    (by decide) (by decide +kernel)
  simp at hJ
end DenseTriangleFree
