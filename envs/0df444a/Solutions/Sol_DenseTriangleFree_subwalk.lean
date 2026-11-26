-- Prove2me | solution 1 for DenseTriangleFree.subwalk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:55:51.17442+00:00
-- url     : https://prove2.me/submissions/768f450f-16cb-4559-b5bf-970ea7d602bf

module
public import Mathlib
public import Definitions.Def_JinLib_KeyLemma
public import Definitions.Def_JinLib_Bipartite
public import Theorems.Thm_DenseTriangleFree_succ_mod_cases

set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}
namespace DenseTriangleFree
theorem _root_.solution {a : V} {c : ℕ → V} (hc : ∀ i, G.Adj (c i) (c (i + 1)))
    (hn : ∀ i, ¬ G.Adj a (c i)) (s L : ℕ) (hL : 0 < L) (hch : G.Adj (c (s + L - 1)) (c s)) :
    (∀ i, c (s + (i + L) % L) = c (s + i % L)) ∧
    (∀ i, G.Adj (c (s + i % L)) (c (s + (i + 1) % L))) ∧ ∀ i, ¬ G.Adj a (c (s + i % L)) := by
  refine ⟨fun i => by rw [Nat.add_mod_right], fun i => ?_, fun i => hn _⟩
  rcases succ_mod_cases i L hL with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h2, ← add_assoc]; exact hc _
  · rw [h2, add_zero, show s + i % L = s + L - 1 by omega]; exact hch
end DenseTriangleFree
