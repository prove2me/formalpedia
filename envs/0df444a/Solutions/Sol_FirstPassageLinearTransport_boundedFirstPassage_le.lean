-- Prove2me | solution 1 for FirstPassageLinearTransport.boundedFirstPassage_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:08:16.612923+00:00
-- url     : https://prove2.me/submissions/05c4f56a-cb11-46f5-8364-335c422204e4

import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_Pullback
import Theorems.Thm_FirstPassageLinearTransport_boundedFirstPassage_eq_find

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution {Y H n : ℕ}
    (h : ∃ k : ℕ, k ≤ H ∧ orbit k n ≤ Y) :
    boundedFirstPassage Y H n ≤ H := by
  rw [boundedFirstPassage_eq_find h]
  exact (Nat.find_spec h).1
end FirstPassageLinearTransport
