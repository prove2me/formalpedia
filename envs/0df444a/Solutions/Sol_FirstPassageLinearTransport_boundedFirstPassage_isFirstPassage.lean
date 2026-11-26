-- Prove2me | solution 1 for FirstPassageLinearTransport.boundedFirstPassage_isFirstPassage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:26:39.152985+00:00
-- url     : https://prove2.me/submissions/9f395f92-dbab-44be-8674-83e04d4976f4

import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_Pullback
import Theorems.Thm_FirstPassageLinearTransport_boundedFirstPassage_eq_find
import Theorems.Thm_FirstPassageLinearTransport_boundedFirstPassage_le
import Theorems.Thm_FirstPassageLinearTransport_boundedFirstPassage_spec

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution {Y H n : ℕ}
    (h : ∃ k : ℕ, k ≤ H ∧ orbit k n ≤ Y) :
    IsFirstPassage Y n (boundedFirstPassage Y H n) := by
  refine ⟨boundedFirstPassage_spec h, ?_⟩
  intro j hj
  by_contra hnot
  have hjle : orbit j n ≤ Y := by omega
  have htime := boundedFirstPassage_le h
  have hmin : boundedFirstPassage Y H n ≤ j := by
    rw [boundedFirstPassage_eq_find h]
    exact Nat.find_min' h ⟨by omega, hjle⟩
  omega
end FirstPassageLinearTransport
