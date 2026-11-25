-- Prove2me | solution 1 for Erdos919.tensorTop_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:33:35.165832+00:00
-- url     : https://prove2.me/submissions/0c9e9d98-b413-431d-a564-b538dede4fc6

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution

set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919
noncomputable section
namespace Erdos919
theorem _root_.solution {V T α : Type*} (H : SimpleGraph V)
    (hT : ∀ d : T → α, ∃ t₁ t₂, t₁ ≠ t₂ ∧ d t₁ = d t₂)
    (c : (tensorTop H T).Coloring α) : Nonempty (H.Coloring α) := by
  choose t₁ t₂ hne hd using fun v : V => hT (fun t => c (v, t))
  refine ⟨Coloring.mk (fun v => c (v, t₁ v)) ?_⟩
  intro v w hvw heq
  have hd' : c (v, t₁ v) = c (v, t₂ v) := hd v
  by_cases h : t₁ v = t₁ w
  · exact c.valid (show (tensorTop H T).Adj (v, t₂ v) (w, t₁ w) from
      tensorTop_adj.2 ⟨hvw, fun e => hne v (h.trans e.symm)⟩) (hd'.symm.trans heq)
  · exact c.valid (show (tensorTop H T).Adj (v, t₁ v) (w, t₁ w) from tensorTop_adj.2 ⟨hvw, h⟩) heq
end Erdos919
