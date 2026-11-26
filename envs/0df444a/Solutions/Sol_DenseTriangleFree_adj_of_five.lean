-- Prove2me | solution 1 for DenseTriangleFree.adj_of_five
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:55:50.654478+00:00
-- url     : https://prove2.me/submissions/2ceca7c6-49eb-477f-a59a-5caf3152b7fb

module
public import Mathlib
public import Definitions.Def_JinLib_KeyLemma
public import Definitions.Def_JinLib_Bipartite

set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}
namespace DenseTriangleFree
theorem _root_.solution
    (hZ : ∀ (a : V) (U : Fin 5 → V), (∀ i, G.Adj (U i) (U (i + 1))) → ∃ i, G.Adj a (U i))
    (a w0 w1 w2 w3 w4 : V) (e0 : G.Adj w0 w1) (e1 : G.Adj w1 w2) (e2 : G.Adj w2 w3)
    (e3 : G.Adj w3 w4) (e4 : G.Adj w4 w0) :
    G.Adj a w0 ∨ G.Adj a w1 ∨ G.Adj a w2 ∨ G.Adj a w3 ∨ G.Adj a w4 := by
  obtain ⟨i, hi⟩ := hZ a ![w0, w1, w2, w3, w4] (fun i => by fin_cases i <;> assumption)
  fin_cases i <;> simp at hi <;> tauto
end DenseTriangleFree
