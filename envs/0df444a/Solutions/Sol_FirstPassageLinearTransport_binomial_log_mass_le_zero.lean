-- Prove2me | solution 1 for FirstPassageLinearTransport.binomial_log_mass_le_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:53:35.743223+00:00
-- url     : https://prove2.me/submissions/587df67d-2d87-485c-8331-88337c5d6ff6

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_entropy_add_logLikelihood_le_zero
import Theorems.Thm_FirstPassageLinearTransport_binomialLogWeight_eq_mul_binEntropy


set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {p : ℝ} (hp₀ : 0 < p) (hp₁ : p < 1)
    {n k : ℕ} (hk : 0 < k) (hkn : k < n) :
    binomialLogWeight n k + (k : ℝ) * Real.log p +
        ((n - k : ℕ) : ℝ) * Real.log (1 - p) ≤ 0 := by
  have hn : 0 < n := hk.trans hkn
  have hnR : 0 < (n : ℝ) := by positivity
  have hu₀ : 0 < (k : ℝ) / (n : ℝ) := div_pos (by positivity) hnR
  have hu₁ : (k : ℝ) / (n : ℝ) < 1 :=
    (div_lt_one hnR).2 (by exact_mod_cast hkn)
  have hentropy := entropy_add_logLikelihood_le_zero hp₀ hp₁ hu₀ hu₁
  have hmul := mul_le_mul_of_nonneg_left hentropy hnR.le
  rw [binomialLogWeight_eq_mul_binEntropy hk hkn, Nat.cast_sub hkn.le]
  calc
    (n : ℝ) * Real.binEntropy ((k : ℝ) / (n : ℝ)) +
          (k : ℝ) * Real.log p +
          ((n : ℝ) - (k : ℝ)) * Real.log (1 - p) =
        (n : ℝ) *
          (Real.binEntropy ((k : ℝ) / (n : ℝ)) +
            ((k : ℝ) / (n : ℝ)) * Real.log p +
            (1 - (k : ℝ) / (n : ℝ)) * Real.log (1 - p)) := by
      field_simp [hnR.ne']
    _ ≤ (n : ℝ) * 0 := hmul
    _ = 0 := by ring
end FirstPassageLinearTransport
