-- Prove2me | solution 1 for C6BipartiteDomination.ZPart_eq_Z0_union_Z1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:45:47.337576+00:00
-- url     : https://prove2.me/submissions/a4af0141-d2df-4e37-8783-68a205a2c5fd

import Definitions.Def_C6BipartiteDomination_A4
import Definitions.Def_C6BipartiteDomination_A5
import Theorems.Thm_C6BipartiteDomination_mem_Z0Part
import Theorems.Thm_C6BipartiteDomination_mem_Z1Part

set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution (D : Finset V) :
    ZPart G D = Z0Part G D ∪ Z1Part G D := by
  classical
  ext z
  constructor
  · intro hz
    by_cases h0 : z ∈ Z0Part G D
    · exact Finset.mem_union_left _ h0
    · apply Finset.mem_union_right
      rw [mem_Z1Part]
      refine ⟨hz, ?_⟩
      by_contra hNo
      apply h0
      rw [mem_Z0Part]
      exact ⟨hz, by simpa using hNo⟩
  · intro hz
    rcases Finset.mem_union.mp hz with h0 | h1
    · exact (mem_Z0Part G D z).mp h0 |>.1
    · exact (mem_Z1Part G D z).mp h1 |>.1
end C6BipartiteDomination
