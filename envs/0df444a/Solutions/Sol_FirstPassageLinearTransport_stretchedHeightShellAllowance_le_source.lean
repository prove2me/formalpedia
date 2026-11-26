-- Prove2me | solution 1 for FirstPassageLinearTransport.stretchedHeightShellAllowance_le_source
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:57:13.851751+00:00
-- url     : https://prove2.me/submissions/96ae5228-2357-4cb1-8f53-1d482fa5dd24

import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_RawNaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_StretchedExceptionalCount
import Definitions.Def_FirstPassageLinearTransport_StretchedRelativeHeight
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell



set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {zeta alpha : ℝ} (hzeta : 0 ≤ zeta) (halpha : 0 ≤ alpha)
    {M n : ℕ} (hn : n ∈ dyadicShell M) :
    stretchedHeightShellAllowance zeta alpha M ≤
      Real.exp (zeta * (Real.log n) ^ alpha) := by
  have hlower : (2 : ℝ) ^ M ≤ (n : ℝ) := by
    exact_mod_cast (mem_dyadicShell.mp hn).1
  have hlogLower : (M : ℝ) * Real.log 2 ≤ Real.log n := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ M) hlower
    rw [Real.log_pow] at h
    exact h
  have hbase0 : 0 ≤ (M : ℝ) * Real.log 2 :=
    mul_nonneg (Nat.cast_nonneg M)
      (Real.log_pos (by norm_num)).le
  have hpowLe : ((M : ℝ) * Real.log 2) ^ alpha ≤
      (Real.log n) ^ alpha :=
    Real.rpow_le_rpow hbase0 hlogLower halpha
  unfold stretchedHeightShellAllowance
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hpowLe hzeta)
end FirstPassageLinearTransport
