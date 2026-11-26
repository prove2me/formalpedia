-- Prove2me | solution 1 for FirstPassageLinearTransport.boundedFirstPassage_eq_find
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:04:26.784797+00:00
-- url     : https://prove2.me/submissions/b15b0df2-a602-4b6a-bfa2-82dd975332b8

import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_Pullback

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution {Y H n : ℕ}
    (h : ∃ k : ℕ, k ≤ H ∧ orbit k n ≤ Y) :
    boundedFirstPassage Y H n = Nat.find h := by
  classical
  unfold boundedFirstPassage
  rw [dif_pos h]
end FirstPassageLinearTransport
