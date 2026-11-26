-- Prove2me | solution 1 for FirstPassageLinearTransport.bounded_passage_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:26:43.036291+00:00
-- url     : https://prove2.me/submissions/dcba3da2-c8d1-4a15-9120-4664bc7439ab

import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_Pullback
import Theorems.Thm_FirstPassageLinearTransport_terminal_witness

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution {r eta : ℝ} (p : StageSetup r eta)
    {M n : ℕ} (hM : p.M0 ≤ M) (hnShell : n ∈ dyadicShell M)
    (hnGood : n ∈ initialWindowGood eta) :
    ∃ k : ℕ, k ≤ M ∧ orbit k n ≤ targetScale r M :=
  ⟨M, le_rfl, terminal_witness p hM hnShell hnGood⟩
end FirstPassageLinearTransport
