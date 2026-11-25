-- Prove2me | solution 1 for ChvatalPosa.chvatalCond_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:19:07.604241+00:00
-- url     : https://prove2.me/submissions/0acb22a5-097f-482b-9a32-02f3c0716aa3

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
theorem _root_.solution {H H' : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel H'.Adj]
    (hle : H ≤ H') (h : ChvatalCond H) : ChvatalCond H' := by
  intro i hi hin hprem
  have hd : ∀ w, H.degree w ≤ H'.degree w := fun w => degree_le_of_le hle
  have h1 : i ≤ #{v | H.degree v ≤ i} := by
    refine hprem.trans (card_le_card ?_)
    intro w; simp only [mem_filter, mem_univ, true_and]; intro hw; exact (hd w).trans hw
  refine (h i hi hin h1).trans (card_le_card ?_)
  intro w; simp only [mem_filter, mem_univ, true_and]; intro hw; exact hw.trans (hd w)
end ChvatalPosa
