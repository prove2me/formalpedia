-- Prove2me | solution 1 for C6BipartiteDomination.mem_paper11K4Supports
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:57:18.634587+00:00
-- url     : https://prove2.me/submissions/9808cc13-96aa-4d57-86ae-51d5930b5b62

import Definitions.Def_C6BipartiteDomination_PaperSection10
import Definitions.Def_C6BipartiteDomination_PaperSection11

set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {D : Finset V} {w : V}
    (hw : w ∈ paper11K4Supports G D) :
    w ∈ SPart G D ∧ externalCharge G D w < 0 ∧ kCharge G D w = 4 := by
  simp only [paper11K4Supports, paper11NegativeSupports, Finset.mem_filter] at hw
  exact ⟨hw.1.1, hw.1.2, hw.2⟩
end C6BipartiteDomination
