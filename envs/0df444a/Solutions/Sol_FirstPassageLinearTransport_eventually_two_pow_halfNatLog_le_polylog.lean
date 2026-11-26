-- Prove2me | solution 1 for FirstPassageLinearTransport.eventually_two_pow_halfNatLog_le_polylog
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:50:29.356262+00:00
-- url     : https://prove2.me/submissions/ed2a200c-5d1e-4424-8804-9990a445dbde

import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_PolylogExceptionalCount
import Theorems.Thm_FirstPassageLinearTransport_tendsto_halfNatLogTwo_atTop
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
    {kappa : ℝ} (_hkappa : 0 ≤ kappa) :
    ∀ᶠ N : ℕ in atTop,
      (2 : ℝ) ^ ((Nat.log 2 N) / 2) ≤
        (N : ℝ) *
          ((((Nat.log 2 N) / 2 : ℕ) : ℝ) + 2) ^ (-kappa) := by
  let b : ℝ := Real.log 2 / 2
  have hb : 0 < b := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  have htReal : Tendsto
      (fun x : ℝ => x ^ kappa * Real.exp (-(b * x)))
      atTop (nhds 0) :=
    by simpa [neg_mul] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero kappa b hb
  have hKT := tendsto_halfNatLogTwo_atTop
  have hxT : Tendsto
      (fun N : ℕ => (((Nat.log 2 N) / 2 : ℕ) : ℝ) + 2)
      atTop atTop :=
    tendsto_atTop_add_const_right atTop (2 : ℝ)
      (tendsto_natCast_atTop_atTop.comp hKT)
  have hsmall : ∀ᶠ N : ℕ in atTop,
      (((((Nat.log 2 N) / 2 : ℕ) : ℝ) + 2) ^ kappa) *
          Real.exp (-(b * ((((Nat.log 2 N) / 2 : ℕ) : ℝ) + 2))) ≤ 1 :=
    (htReal.comp hxT).eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hsmall,
      (hKT.eventually (eventually_ge_atTop (2 : ℕ))),
      eventually_ge_atTop (1 : ℕ)] with N hsmall hK2 hN1
  let L := Nat.log 2 N
  let K := L / 2
  let x : ℝ := (K : ℝ) + 2
  have hx : 0 < x := by dsimp [x]; positivity
  have hxpow : 0 < x ^ kappa := Real.rpow_pos_of_pos hx _
  have hK2R : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK2
  have hrate : b * x ≤ Real.log 2 * (K : ℝ) := by
    dsimp [b, x]
    nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hexp :
      Real.exp (-(Real.log 2 * (K : ℝ))) ≤
        Real.exp (-(b * x)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hprod :
      x ^ kappa * Real.exp (-(Real.log 2 * (K : ℝ))) ≤ 1 := by
    calc
      x ^ kappa * Real.exp (-(Real.log 2 * (K : ℝ))) ≤
          x ^ kappa * Real.exp (-(b * x)) :=
        mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg hx.le _)
      _ ≤ 1 := by simpa [L, K, x, b] using hsmall
  have hxpow_le : x ^ kappa ≤ (2 : ℝ) ^ K := by
    have hmul := mul_le_mul_of_nonneg_right hprod
      (Real.exp_pos (Real.log 2 * (K : ℝ))).le
    have hcancel :
        Real.exp (-(Real.log 2 * (K : ℝ))) *
            Real.exp (Real.log 2 * (K : ℝ)) = 1 := by
      rw [← Real.exp_add]
      simp
    have hexpPow :
        Real.exp (Real.log 2 * (K : ℝ)) = (2 : ℝ) ^ K := by
      rw [show Real.log 2 * (K : ℝ) = Real.log ((2 : ℝ) ^ K) by
        rw [Real.log_pow]
        ring]
      exact Real.exp_log (by positivity)
    calc
      x ^ kappa = x ^ kappa * 1 := by ring
      _ = x ^ kappa *
          (Real.exp (-(Real.log 2 * (K : ℝ))) *
            Real.exp (Real.log 2 * (K : ℝ))) := by rw [hcancel]
      _ = (x ^ kappa * Real.exp (-(Real.log 2 * (K : ℝ)))) *
            Real.exp (Real.log 2 * (K : ℝ)) := by ring
      _ ≤ 1 * Real.exp (Real.log 2 * (K : ℝ)) := hmul
      _ = (2 : ℝ) ^ K := by rw [one_mul, hexpPow]
  have hone : 1 ≤ (2 : ℝ) ^ K * x ^ (-kappa) := by
    rw [Real.rpow_neg hx.le]
    apply (le_div_iff₀ hxpow).2
    simpa using hxpow_le
  have hKK : (2 : ℝ) ^ K ≤
      (2 : ℝ) ^ (2 * K) * x ^ (-kappa) := by
    calc
      (2 : ℝ) ^ K ≤ (2 : ℝ) ^ K *
          ((2 : ℝ) ^ K * x ^ (-kappa)) := by
        simpa using mul_le_mul_of_nonneg_left hone (by positivity :
          0 ≤ (2 : ℝ) ^ K)
      _ = ((2 : ℝ) ^ K * (2 : ℝ) ^ K) * x ^ (-kappa) := by ring
      _ = (2 : ℝ) ^ (K + K) * x ^ (-kappa) := by rw [pow_add]
      _ = (2 : ℝ) ^ (2 * K) * x ^ (-kappa) := by
        congr 2
        omega
  have h2KL : 2 * K ≤ L := by
    dsimp [K]
    omega
  have hpowKN : (2 : ℝ) ^ (2 * K) ≤ (N : ℝ) := by
    have hpowNat : 2 ^ (2 * K) ≤ N :=
      (Nat.pow_le_pow_right (by omega) h2KL).trans
        (Nat.pow_log_le_self 2 (by omega : N ≠ 0))
    exact_mod_cast hpowNat
  calc
    (2 : ℝ) ^ ((Nat.log 2 N) / 2) = (2 : ℝ) ^ K := by rfl
    _ ≤ (2 : ℝ) ^ (2 * K) * x ^ (-kappa) := hKK
    _ ≤ (N : ℝ) * x ^ (-kappa) :=
      mul_le_mul_of_nonneg_right hpowKN (Real.rpow_nonneg hx.le _)
    _ = (N : ℝ) *
        ((((Nat.log 2 N) / 2 : ℕ) : ℝ) + 2) ^ (-kappa) := by
      rfl
end FirstPassageLinearTransport
