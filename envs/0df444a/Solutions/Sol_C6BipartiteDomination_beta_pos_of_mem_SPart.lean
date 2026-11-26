-- Prove2me | solution 1 for C6BipartiteDomination.beta_pos_of_mem_SPart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:46:53.713652+00:00
-- url     : https://prove2.me/submissions/b35706fd-2044-42cb-8997-d19dab85d59b

import Definitions.Def_C6BipartiteDomination_A6
import Definitions.Def_C6BipartiteDomination_A7
import Theorems.Thm_C6BipartiteDomination_mem_SPart
import Theorems.Thm_C6BipartiteDomination_mem_W0Part
import Theorems.Thm_C6BipartiteDomination_mem_WBPart


set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {D : Finset V} {w : V}
    (hw : w ∈ SPart G D) : 1 ≤ betaCharge G D w := by
  classical
  have hwWB := (mem_SPart G D w).mp hw |>.1
  have hw0 := (mem_WBPart G D w).mp hwWB |>.2
  unfold betaCharge degreeTo
  have hneigh : ∃ b ∈ BPart G D, G.Adj w b := by
    by_contra h
    apply hw0
    rw [mem_W0Part]
    refine ⟨(mem_WBPart G D w).mp hwWB |>.1, ?_⟩
    intro b hb hbw
    exact h ⟨b, hb, hbw.symm⟩
  rcases hneigh with ⟨b, hb, hwb⟩
  have hpos : 0 < ((BPart G D).filter (fun u => G.Adj w u)).card :=
    Finset.card_pos.mpr ⟨b, Finset.mem_filter.mpr ⟨hb, hwb⟩⟩
  omega
end C6BipartiteDomination
