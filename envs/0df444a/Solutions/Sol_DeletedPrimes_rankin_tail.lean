-- Prove2me | solution 1 for DeletedPrimes.rankin_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:59:34.716005+00:00
-- url     : https://prove2.me/submissions/4eef9491-fdfb-4378-9314-9d98e501362a

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}
namespace DeletedPrimes
theorem _root_.solution {σ : ℝ} (hsum : Summable fun d : ℕ => |(muS S d : ℝ)| * (d : ℝ) ^ (-σ))
    (hσ1 : σ ≤ 1) {Z : ℝ} (hZ : 1 ≤ Z) :
    ∑' d : ℕ, (if Z < d then |(muS S d : ℝ)| / d else 0) ≤ unitSum S σ * Z ^ (σ - 1) := by
  have hZ0 : 0 < Z := by linarith
  have hle : ∀ d : ℕ, (if Z < d then |(muS S d : ℝ)| / d else 0) ≤
      Z ^ (σ - 1) * (|(muS S d : ℝ)| * (d : ℝ) ^ (-σ)) := by
    intro d
    split_ifs with h
    · have hd0 : (0 : ℝ) < d := lt_trans hZ0 h
      have h2 : (d : ℝ) ^ (σ - 1) ≤ Z ^ (σ - 1) :=
        Real.rpow_le_rpow_of_nonpos hZ0 h.le (by linarith)
      have h3 : |(muS S d : ℝ)| / d = |(muS S d : ℝ)| * (d : ℝ) ^ (-σ) * (d : ℝ) ^ (σ - 1) := by
        rw [mul_assoc, ← Real.rpow_add hd0, show -σ + (σ - 1) = -1 by ring, Real.rpow_neg_one,
          div_eq_mul_inv]
      rw [h3, mul_comm (Z ^ (σ - 1))]
      exact mul_le_mul_of_nonneg_left h2
        (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hd0.le _))
    · exact mul_nonneg (Real.rpow_nonneg hZ0.le _)
        (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg d) _))
  have hnn : ∀ d : ℕ, 0 ≤ (if Z < d then |(muS S d : ℝ)| / d else 0) := by
    intro d; split_ifs
    · exact div_nonneg (abs_nonneg _) (Nat.cast_nonneg d)
    · exact le_rfl
  have hsum' := hsum.mul_left (Z ^ (σ - 1))
  calc ∑' d : ℕ, (if Z < d then |(muS S d : ℝ)| / d else 0)
      ≤ ∑' d : ℕ, Z ^ (σ - 1) * (|(muS S d : ℝ)| * (d : ℝ) ^ (-σ)) :=
        Summable.tsum_le_tsum hle (hsum'.of_nonneg_of_le hnn hle) hsum'
    _ = unitSum S σ * Z ^ (σ - 1) := by
        rw [tsum_mul_left, unitSum, mul_comm]
end DeletedPrimes
