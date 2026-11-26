-- Prove2me | solution 1 for FirstPassageLinearTransport.log_two_eq_of_mem_dyadicShell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:04:10.1828+00:00
-- url     : https://prove2.me/submissions/9b4d8530-086b-4baf-a406-8e3c1f076884

import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_Envelope
import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution {M n : ℕ}
    (hn : n ∈ dyadicShell M) : Nat.log 2 n = M := by
  have hb := mem_dyadicShell.mp hn
  exact Nat.log_eq_of_pow_le_of_lt_pow hb.1 hb.2
end FirstPassageLinearTransport
