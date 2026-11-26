-- Prove2me | solution 1 for FirstPassageLinearTransport.boundedFirstPassage_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:25:42.089245+00:00
-- url     : https://prove2.me/submissions/4ea2efb5-2605-4efc-807f-f29001ffd65a

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
    orbit (boundedFirstPassage Y H n) n ≤ Y := by
  rw [boundedFirstPassage_eq_find h]
  exact (Nat.find_spec h).2
end FirstPassageLinearTransport
