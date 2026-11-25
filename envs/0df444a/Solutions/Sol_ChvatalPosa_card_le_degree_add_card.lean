-- Prove2me | solution 1 for ChvatalPosa.card_le_degree_add_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:18:44.947355+00:00
-- url     : https://prove2.me/submissions/45f3cc6e-7c37-4892-adb5-d1505b67b0db

module
public import Mathlib
public import Definitions.Def_MengerHamilton_Hamiltonian
public import Definitions.Def_ChvatalPosaLib_ChvatalPosa

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ChvatalPosa
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
omit [DecidableEq V]
namespace ChvatalPosa
theorem _root_.solution (H : SimpleGraph V) [DecidableRel H.Adj] (v : V) (S : Finset V)
    (hS : ∀ w, ¬ H.Adj v w → w ∈ S) : Fintype.card V ≤ H.degree v + #S := by
  classical
  rw [← card_neighborFinset_eq_degree, ← card_univ]
  refine (card_le_card ?_).trans (card_union_le _ _)
  intro w _
  by_cases hw : H.Adj v w
  · exact mem_union_left _ ((mem_neighborFinset _ _ _).2 hw)
  · exact mem_union_right _ (hS w hw)
end ChvatalPosa
