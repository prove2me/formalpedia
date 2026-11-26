-- Prove2me | solution 1 for FirstPassageLinearTransport.shell_log_le_rank_add_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:34:39.897337+00:00
-- url     : https://prove2.me/submissions/0301a4eb-bba8-41fb-a11c-f8777c3f8f2f

import Definitions.Def_FirstPassageLinearTransport_SharpJointExceptionalOrders
import Definitions.Def_FirstPassageLinearTransport_CriticalEndpointConsequences
import Definitions.Def_FirstPassageLinearTransport_FixedJointExceptionalOrder
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell



set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {M n : ℕ} (hn : n ∈ dyadicShell M) :
    Real.log n ≤ (M : ℝ) + 2 := by
  have hnPos : 0 < n := by
    have hpow : 0 < 2 ^ M := by positivity
    exact hpow.trans_le (mem_dyadicShell.mp hn).1
  have hnUpper : (n : ℝ) < (2 : ℝ) ^ (M + 1) := by
    exact_mod_cast (mem_dyadicShell.mp hn).2
  have hlog := Real.strictMonoOn_log
    (Set.mem_Ioi.mpr (by exact_mod_cast hnPos))
    (Set.mem_Ioi.mpr (by positivity : (0 : ℝ) < (2 : ℝ) ^ (M + 1)))
    hnUpper
  rw [Real.log_pow] at hlog
  have hlog2lt : Real.log 2 < 1 :=
    Real.log_two_lt_d9.trans (by norm_num)
  push_cast at hlog
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  nlinarith
end FirstPassageLinearTransport
