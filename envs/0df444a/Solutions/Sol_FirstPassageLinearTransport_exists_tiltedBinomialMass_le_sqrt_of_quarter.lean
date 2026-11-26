-- Prove2me | solution 1 for FirstPassageLinearTransport.exists_tiltedBinomialMass_le_sqrt_of_quarter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:55:00.866364+00:00
-- url     : https://prove2.me/submissions/84380d53-a509-45ee-8190-a9a09288b60c

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_exp_binomialLogWeight_mul_powers_le_one
import Theorems.Thm_FirstPassageLinearTransport_exists_choose_le_stirlingCore_ratio
import Theorems.Thm_FirstPassageLinearTransport_stirlingCore_ratio_eq_sqrt_exp
import Theorems.Thm_FirstPassageLinearTransport_stirlingSqrtPrefactor_le_of_quarter


set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {p : ℝ} (hp₀ : 0 < p) (hp₁ : p < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ n k : ℕ, 0 < n → 0 < k → k < n →
        (n : ℝ) / 4 ≤ (k : ℝ) →
        (n : ℝ) / 4 ≤ ((n - k : ℕ) : ℝ) →
        tiltedBinomialMass p n k ≤ C / Real.sqrt n := by
  obtain ⟨C₀, hC₀, hchoose⟩ := exists_choose_le_stirlingCore_ratio
  refine ⟨4 * C₀, mul_pos (by norm_num) hC₀, ?_⟩
  intro n k hn hk hkn hkLower hnkLower
  have hchoose' := hchoose n k hk hkn
  have hchoose'' :
      (n.choose k : ℝ) ≤
        C₀ * (Real.sqrt (2 * n) /
          (Real.sqrt (2 * k) * Real.sqrt (2 * (n - k))) *
            Real.exp (binomialLogWeight n k)) := by
    calc
      (n.choose k : ℝ) ≤
          C₀ * stirlingCore n /
            (stirlingCore k * stirlingCore (n - k)) := hchoose'
      _ = C₀ *
          (stirlingCore n /
            (stirlingCore k * stirlingCore (n - k))) := by ring
      _ = C₀ * (Real.sqrt (2 * n) /
          (Real.sqrt (2 * k) * Real.sqrt (2 * (n - k))) *
            Real.exp (binomialLogWeight n k)) := by
        rw [stirlingCore_ratio_eq_sqrt_exp hk hkn]
  have hpref := stirlingSqrtPrefactor_le_of_quarter
    hn hk hkn hkLower hnkLower
  have hweight := exp_binomialLogWeight_mul_powers_le_one
    hp₀ hp₁ hk hkn
  have hpNonneg : 0 ≤ p ^ k * (1 - p) ^ (n - k) :=
    mul_nonneg (pow_nonneg hp₀.le _) (pow_nonneg (sub_nonneg.mpr hp₁.le) _)
  have hCNonneg : 0 ≤ C₀ := hC₀.le
  have hprefNonneg :
      0 ≤ Real.sqrt (2 * n) /
        (Real.sqrt (2 * k) * Real.sqrt (2 * (n - k))) := by positivity
  have hweightNonneg :
      0 ≤ Real.exp (binomialLogWeight n k) * p ^ k *
        (1 - p) ^ (n - k) :=
    mul_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg hp₀.le _))
      (pow_nonneg (sub_nonneg.mpr hp₁.le) _)
  have hboundNonneg : 0 ≤ C₀ * (4 / Real.sqrt n) := by positivity
  unfold tiltedBinomialMass
  calc
    (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k) ≤
        (C₀ * (Real.sqrt (2 * n) /
          (Real.sqrt (2 * k) * Real.sqrt (2 * (n - k))) *
            Real.exp (binomialLogWeight n k))) *
              p ^ k * (1 - p) ^ (n - k) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hchoose'' (pow_nonneg hp₀.le _))
        (pow_nonneg (sub_nonneg.mpr hp₁.le) _)
    _ = C₀ *
        (Real.sqrt (2 * n) /
          (Real.sqrt (2 * k) * Real.sqrt (2 * (n - k)))) *
        (Real.exp (binomialLogWeight n k) * p ^ k *
          (1 - p) ^ (n - k)) := by ring
    _ ≤ C₀ * (4 / Real.sqrt n) * 1 := by
      calc
        C₀ * (Real.sqrt (2 * n) /
              (Real.sqrt (2 * k) * Real.sqrt (2 * (n - k)))) *
            (Real.exp (binomialLogWeight n k) * p ^ k *
              (1 - p) ^ (n - k)) ≤
            C₀ * (4 / Real.sqrt n) *
              (Real.exp (binomialLogWeight n k) * p ^ k *
                (1 - p) ^ (n - k)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpref hCNonneg) hweightNonneg
        _ ≤ C₀ * (4 / Real.sqrt n) * 1 :=
          mul_le_mul_of_nonneg_left hweight hboundNonneg
    _ = (4 * C₀) / Real.sqrt n := by ring
end FirstPassageLinearTransport
