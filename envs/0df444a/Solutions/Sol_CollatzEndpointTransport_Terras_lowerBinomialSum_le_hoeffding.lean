-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.lowerBinomialSum_le_hoeffding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:26:11.442219+00:00
-- url     : https://prove2.me/submissions/c96f3b6c-2155-4549-98de-47ab888756be

import Definitions.Def_CollatzEndpointTransport_Common_TerrasParityBijection
import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
import Theorems.Thm_CollatzEndpointTransport_Terras_pow_mul_lowerBinomialSum_le
import Theorems.Thm_CollatzEndpointTransport_Terras_one_add_exp_neg_four_mul_le

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset
namespace CollatzEndpointTransport.Terras
theorem _root_.solution
    {H K : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (hcut : (K : ℝ) ≤ (1 / 2 - t) * H) :
    (lowerBinomialSum H K : ℝ) ≤
      (2 : ℝ) ^ H * Real.exp (-2 * t ^ 2 * H) := by
  have hKHreal : (K : ℝ) ≤ H := by
    calc
      (K : ℝ) ≤ (1 / 2 - t) * H := hcut
      _ ≤ H := by
        have hH : (0 : ℝ) ≤ H := Nat.cast_nonneg H
        nlinarith
  have hKH : K ≤ H := by exact_mod_cast hKHreal
  let x : ℝ := Real.exp (-4 * t)
  have hx0 : 0 < x := by
    dsimp [x]
    positivity
  have hx1 : x ≤ 1 := by
    dsimp [x]
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have htail :
      x ^ K * (lowerBinomialSum H K : ℝ) ≤ (1 + x) ^ H :=
    pow_mul_lowerBinomialSum_le hx0.le hx1 hKH
  let z : ℝ := -2 * t + 2 * t ^ 2
  have hbase : 1 + x ≤ 2 * Real.exp z := by
    dsimp [x, z]
    exact one_add_exp_neg_four_mul_le t
  have hpow : (1 + x) ^ H ≤ (2 * Real.exp z) ^ H := by
    exact pow_le_pow_left₀ (by positivity) hbase H
  have hnonpos : -4 * t ≤ 0 := by nlinarith
  have hcutScaled :
      (-4 * t) * ((1 / 2 - t) * H) ≤ (-4 * t) * K :=
    mul_le_mul_of_nonpos_left hcut hnonpos
  have harg :
      (H : ℝ) * z ≤ -2 * t ^ 2 * H + (K : ℝ) * (-4 * t) := by
    dsimp [z]
    nlinarith
  have hexp :
      Real.exp ((H : ℝ) * z) ≤
        Real.exp (-2 * t ^ 2 * H + (K : ℝ) * (-4 * t)) :=
    Real.exp_le_exp.mpr harg
  have htarget :
      (1 + x) ^ H ≤
        ((2 : ℝ) ^ H * Real.exp (-2 * t ^ 2 * H)) * x ^ K := by
    calc
      (1 + x) ^ H ≤ (2 * Real.exp z) ^ H := hpow
      _ = (2 : ℝ) ^ H * Real.exp ((H : ℝ) * z) := by
        rw [mul_pow, ← Real.exp_nat_mul]
      _ ≤ (2 : ℝ) ^ H *
          Real.exp (-2 * t ^ 2 * H + (K : ℝ) * (-4 * t)) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = ((2 : ℝ) ^ H * Real.exp (-2 * t ^ 2 * H)) * x ^ K := by
        dsimp [x]
        rw [← Real.exp_nat_mul, Real.exp_add]
        ring
  have hmul :
      x ^ K * (lowerBinomialSum H K : ℝ) ≤
        ((2 : ℝ) ^ H * Real.exp (-2 * t ^ 2 * H)) * x ^ K :=
    htail.trans htarget
  exact (mul_le_mul_iff_right₀ (pow_pos hx0 K)).mp (by
    simpa [mul_comm] using hmul)
end CollatzEndpointTransport.Terras
