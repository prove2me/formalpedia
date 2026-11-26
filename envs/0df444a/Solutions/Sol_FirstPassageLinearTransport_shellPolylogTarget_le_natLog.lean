-- Prove2me | solution 1 for FirstPassageLinearTransport.shellPolylogTarget_le_natLog
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:43:55.164851+00:00
-- url     : https://prove2.me/submissions/ef0f4660-db86-4560-bfb4-cdaf51b3052f

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
    {A : ℝ} (hA : 0 ≤ A) {M n : ℕ}
    (hnShell : n ∈ dyadicShell M) (hlogn : 1 ≤ Real.log n) :
    2 * (((M : ℝ) + 2) ^ A) ≤
      fixedPolylogTargetConstant A * (Real.log n) ^ A := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnLower : ((2 : ℕ) ^ M : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (mem_dyadicShell.mp hnShell).1
  have hlogLower : (M : ℝ) * Real.log 2 ≤ Real.log n := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ M)
      hnLower
    rw [Real.log_pow] at h
    exact h
  have hM : (M : ℝ) ≤ Real.log n / Real.log 2 := by
    rw [le_div_iff₀ hlog2]
    simpa [mul_comm] using hlogLower
  have hbase : (M : ℝ) + 2 ≤
      (1 / Real.log 2 + 2) * Real.log n := by
    calc
      (M : ℝ) + 2 ≤ Real.log n / Real.log 2 + 2 * Real.log n := by
        gcongr
        linarith
      _ = (1 / Real.log 2 + 2) * Real.log n := by ring
  have hleft0 : 0 ≤ (M : ℝ) + 2 := by positivity
  have hright0 : 0 ≤ (1 / Real.log 2 + 2) * Real.log n := by
    positivity
  have hpow := Real.rpow_le_rpow hleft0 hbase hA
  calc
    2 * (((M : ℝ) + 2) ^ A) ≤
        2 * (((1 / Real.log 2 + 2) * Real.log n) ^ A) :=
      mul_le_mul_of_nonneg_left hpow (by norm_num)
    _ = fixedPolylogTargetConstant A * (Real.log n) ^ A := by
      rw [Real.mul_rpow (by positivity) (by linarith)]
      simp only [fixedPolylogTargetConstant]
      ring
end FirstPassageLinearTransport
