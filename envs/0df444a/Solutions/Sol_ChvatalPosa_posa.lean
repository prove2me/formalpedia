-- Prove2me | solution 1 for ChvatalPosa.posa
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:37:11.040908+00:00
-- url     : https://prove2.me/submissions/b5c6abfb-db7e-46ff-bebd-bd781fde4055

module
public import Mathlib
public import Definitions.Def_MengerHamilton_Hamiltonian
public import Definitions.Def_ChvatalPosaLib_ChvatalPosa
public import Theorems.Thm_ChvatalPosa_chvatal

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ChvatalPosa
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
namespace ChvatalPosa
theorem _root_.solution (hn : 3 ≤ Fintype.card V)
    (h₁ : ∀ k : ℕ, 1 ≤ k → 2 * k < Fintype.card V - 1 → #{v | G.degree v ≤ k} < k)
    (h₂ : Odd (Fintype.card V) →
      #{v | G.degree v ≤ (Fintype.card V - 1) / 2} ≤ (Fintype.card V - 1) / 2) :
    G.IsHamiltonian := by
  refine chvatal G hn fun i hi hin hprem => ?_
  set n := Fintype.card V
  by_cases hlt : 2 * i < n - 1
  · have := h₁ i hi hlt; omega
  · have hn' : n = 2 * i + 1 := by omega
    have hodd : Odd n := ⟨i, by omega⟩
    have hhalf : (n - 1) / 2 = i := by omega
    have hle := h₂ hodd
    rw [hhalf] at hle
    have hsplit := card_filter_add_card_filter_not (s := (univ : Finset V))
      (fun w => G.degree w ≤ i)
    rw [card_univ] at hsplit
    have hsub : ({w | ¬ G.degree w ≤ i} : Finset V) ⊆ ({w | n - i ≤ G.degree w} : Finset V) := by
      intro w; simp only [mem_filter, mem_univ, true_and]; omega
    have := card_le_card hsub
    omega
end ChvatalPosa
