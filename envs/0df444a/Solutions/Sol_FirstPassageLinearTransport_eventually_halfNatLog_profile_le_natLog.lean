-- Prove2me | solution 1 for FirstPassageLinearTransport.eventually_halfNatLog_profile_le_natLog
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:50:45.25106+00:00
-- url     : https://prove2.me/submissions/6672749b-e514-4856-841d-5777c01384d7

import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_PolylogExceptionalCount
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {kappa : ℝ} (hkappa : 0 ≤ kappa) :
    ∀ᶠ N : ℕ in atTop,
      ((((Nat.log 2 N) / 2 : ℕ) : ℝ) + 2) ^ (-kappa) ≤
        (2 * Real.log 2) ^ kappa * (Real.log N) ^ (-kappa) := by
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN2
  let L := Nat.log 2 N
  let K := L / 2
  let x : ℝ := (K : ℝ) + 2
  let q : ℝ := 2 * Real.log 2
  have hNpos : 0 < N := by omega
  have hNRpos : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq : 0 < q := by
    dsimp [q]
    positivity
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN2)
  have hx : 0 < x := by
    dsimp [x]
    positivity
  have hLX : (N : ℝ) < (2 : ℝ) ^ (L + 1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num) N
  have hlogUpper : Real.log N ≤ ((L : ℝ) + 1) * Real.log 2 := by
    have h := Real.log_le_log hNRpos (le_of_lt hLX)
    rwa [Real.log_pow, Nat.cast_add, Nat.cast_one] at h
  have hLhalfNat : L ≤ 2 * K + 1 := by
    dsimp [K]
    omega
  have hLhalf : (L : ℝ) + 1 ≤ 2 * x := by
    have hcast : (L : ℝ) ≤ 2 * (K : ℝ) + 1 := by
      exact_mod_cast hLhalfNat
    dsimp [x]
    linarith
  have hlogx : Real.log N ≤ q * x := by
    calc
      Real.log N ≤ ((L : ℝ) + 1) * Real.log 2 := hlogUpper
      _ ≤ (2 * x) * Real.log 2 :=
        mul_le_mul_of_nonneg_right hLhalf hlog2.le
      _ = q * x := by
        dsimp [q]
        ring
  have hqx : Real.log N / q ≤ x := (div_le_iff₀ hq).2 (by
    simpa [mul_comm] using hlogx)
  have hmono : x ^ (-kappa) ≤ (Real.log N / q) ^ (-kappa) :=
    Real.rpow_le_rpow_of_nonpos
      (div_pos hlogN hq) hqx (neg_nonpos.mpr hkappa)
  have hrewrite :
      (Real.log N / q) ^ (-kappa) =
        q ^ kappa * (Real.log N) ^ (-kappa) := by
    rw [Real.div_rpow hlogN.le hq.le]
    rw [Real.rpow_neg hq.le]
    field_simp
  simpa [L, K, x, q, hrewrite] using hmono.trans_eq hrewrite
end FirstPassageLinearTransport
