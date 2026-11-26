-- Prove2me | solution 1 for FirstPassageLinearTransport.mem_dyadicShell_log
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:12:55.865902+00:00
-- url     : https://prove2.me/submissions/67dc5b21-ca85-448e-8e6c-3687fc816b91

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_FirstPassageLinearTransport_Parameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_Bootstrap
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution {n : ℕ} (hn : 0 < n) :
    n ∈ dyadicShell (Nat.log 2 n) := by
  rw [mem_dyadicShell]
  exact ⟨Nat.pow_log_le_self 2 hn.ne',
    Nat.lt_pow_succ_log_self (by norm_num) n⟩
end FirstPassageLinearTransport
