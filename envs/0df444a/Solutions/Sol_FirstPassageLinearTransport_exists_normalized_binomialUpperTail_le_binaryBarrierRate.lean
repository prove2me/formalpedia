-- Prove2me | solution 1 for FirstPassageLinearTransport.exists_normalized_binomialUpperTail_le_binaryBarrierRate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:54:55.527854+00:00
-- url     : https://prove2.me/submissions/26af18dd-96af-43a9-aa4d-b22eeae6fbae

import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Interval.Finset.Nat
import Definitions.Def_FirstPassageLinearTransport_EntropyBarrier
import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Theorems.Thm_FirstPassageLinearTransport_normalized_binomialLogWeight_eq_binaryBarrierRate
import Theorems.Thm_FirstPassageLinearTransport_exists_binomialUpperTail_le_sqrt_exp

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {t₀ : ℝ} (ht₀ : 0 < t₀) :
    ∃ C : ℝ, 0 < C ∧
      ∀ r k : ℕ, 0 < r → 0 < k → k < r →
        (r : ℝ) * (1 / 2 + t₀) ≤ (k : ℝ) →
        (r : ℝ) / 4 ≤ (k : ℝ) →
        (r : ℝ) / 4 ≤ ((r - k : ℕ) : ℝ) →
        (binomialUpperTail r k : ℝ) / (2 : ℝ) ^ r ≤
          (C / Real.sqrt r) *
            Real.exp (-((r : ℝ) *
              binaryBarrierRate ((k : ℝ) / (r : ℝ) - 1 / 2))) := by
  obtain ⟨C, hC, htail⟩ := exists_binomialUpperTail_le_sqrt_exp ht₀
  refine ⟨C, hC, ?_⟩
  intro r k hr hk hkr hgap hkLower hrkLower
  have h := htail r k hr hk hkr hgap hkLower hrkLower
  have hpowPos : 0 < (2 : ℝ) ^ r := by positivity
  have hpow :
      (2 : ℝ) ^ r = Real.exp ((r : ℝ) * Real.log 2) := by
    calc
      (2 : ℝ) ^ r = (Real.exp (Real.log 2)) ^ r := by
        rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ = Real.exp ((r : ℝ) * Real.log 2) := by
        rw [← Real.exp_nat_mul]
  have hnormalized :
      Real.exp (binomialLogWeight r k) / (2 : ℝ) ^ r =
        Real.exp (-((r : ℝ) *
          binaryBarrierRate ((k : ℝ) / (r : ℝ) - 1 / 2))) := by
    rw [hpow, ← Real.exp_sub,
      normalized_binomialLogWeight_eq_binaryBarrierRate hk hkr]
  calc
    (binomialUpperTail r k : ℝ) / (2 : ℝ) ^ r ≤
        ((C / Real.sqrt r) * Real.exp (binomialLogWeight r k)) /
          (2 : ℝ) ^ r := (div_le_div_iff_of_pos_right hpowPos).2 h
    _ = (C / Real.sqrt r) *
          (Real.exp (binomialLogWeight r k) / (2 : ℝ) ^ r) := by ring
    _ = (C / Real.sqrt r) *
          Real.exp (-((r : ℝ) *
            binaryBarrierRate ((k : ℝ) / (r : ℝ) - 1 / 2))) := by
      rw [hnormalized]
end FirstPassageLinearTransport
