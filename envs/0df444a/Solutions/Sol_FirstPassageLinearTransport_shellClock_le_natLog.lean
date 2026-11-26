-- Prove2me | solution 1 for FirstPassageLinearTransport.shellClock_le_natLog
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:45:05.788977+00:00
-- url     : https://prove2.me/submissions/84f1f4cc-9f0a-4748-a7bb-a1326fd7c6b6

import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_PolylogTarget
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {c : ℝ} (hc : 0 ≤ c) {M n : ℕ} (hnShell : n ∈ dyadicShell M) :
    c * (M : ℝ) * Real.log 2 ≤ c * Real.log n := by
  have hnLower : ((2 : ℕ) ^ M : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (mem_dyadicShell.mp hnShell).1
  have hlogLower : (M : ℝ) * Real.log 2 ≤ Real.log n := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ M)
      hnLower
    rw [Real.log_pow] at h
    exact h
  simpa [mul_assoc] using mul_le_mul_of_nonneg_left hlogLower hc
end FirstPassageLinearTransport
