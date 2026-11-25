-- Prove2me | solution 1 for Erdos919.shift_colorableOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:35:33.220158+00:00
-- url     : https://prove2.me/submissions/c149aef6-9a8d-4815-a34c-4487d43d051b

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution
public import Theorems.Thm_Erdos919_shift_adj
public import Theorems.Thm_Erdos919_diffColor_ne

set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919
noncomputable section
variable (I : Type*) [LinearOrder I]
variable {I}
namespace Erdos919
theorem _root_.solution {T : Type*} [LinearOrder T] [WellFoundedLT T] [Inhabited T]
    (S : Set I) (f : I → T → Bool) (hf : Set.InjOn f S) :
    ColorableOn (shift I) {p | p.1.1 ∈ S ∧ p.1.2 ∈ S} (T × Bool) := by
  refine ⟨fun p => diffColor (f p.1.1) (f p.1.2), ?_⟩
  intro p hp q hq hpq
  have hne : ∀ r : {p : I × I // p.1 < p.2}, r.1.1 ∈ S → r.1.2 ∈ S → f r.1.1 ≠ f r.1.2 :=
    fun r h1 h2 e => (ne_of_lt r.2) (hf h1 h2 e)
  have e1 := hne p hp.1 hp.2
  have e2 := hne q hq.1 hq.2
  show diffColor (f p.1.1) (f p.1.2) ≠ diffColor (f q.1.1) (f q.1.2)
  rcases shift_adj.1 hpq with h | h
  · rw [h] at e1 ⊢
    exact diffColor_ne e1 e2
  · rw [← h] at e1 ⊢
    exact (diffColor_ne e2 e1).symm
end Erdos919
