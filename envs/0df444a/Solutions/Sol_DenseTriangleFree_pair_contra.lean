-- Prove2me | solution 1 for DenseTriangleFree.pair_contra
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:49:48.500524+00:00
-- url     : https://prove2.me/submissions/454e7e4a-8bb3-4b34-9ff1-ced2520306aa

module
public import Mathlib
public import Definitions.Def_JinLib_Heavy
public import Definitions.Def_JinLib_Pairs
public import Theorems.Thm_DenseTriangleFree_mem_sSet

set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
open SimpleGraph
variable {V : Type*} (G : SimpleGraph V)
namespace DenseTriangleFree
theorem _root_.solution {m : ℕ}
    (hbest : ∀ (b : V) (W : Fin 5 → V), IsPair G b W → (sSet G b W).card ≤ m)
    (b w0 w1 w2 w3 w4 : V) (e0 : G.Adj w0 w1) (e1 : G.Adj w1 w2) (e2 : G.Adj w2 w3)
    (e3 : G.Adj w3 w4) (e4 : G.Adj w4 w0)
    (n0 : ¬ G.Adj b w0) (n1 : ¬ G.Adj b w1) (n2 : ¬ G.Adj b w2) (n3 : ¬ G.Adj b w3)
    (n4 : ¬ G.Adj b w4) (Q : Finset (Fin 5)) (hQ : m < Q.card)
    (hw : ∀ i ∈ Q, ∃ t, G.Adj b t ∧ G.Adj (![w0, w1, w2, w3, w4] (i - 1)) t ∧
      G.Adj (![w0, w1, w2, w3, w4] (i + 1)) t) : False := by
  have hp : IsPair G b ![w0, w1, w2, w3, w4] := by
    refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i <;> assumption
  have h1 := hbest _ _ hp
  have h2 : Q ⊆ sSet G b ![w0, w1, w2, w3, w4] := fun i hi => (mem_sSet G).2 (hw i hi)
  have := Finset.card_le_card h2
  omega
end DenseTriangleFree
