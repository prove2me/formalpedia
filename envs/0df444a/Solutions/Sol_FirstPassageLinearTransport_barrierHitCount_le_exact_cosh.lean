-- Prove2me | solution 1 for FirstPassageLinearTransport.barrierHitCount_le_exact_cosh
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:38:29.51421+00:00
-- url     : https://prove2.me/submissions/8791b0af-3e15-4438-9035-87846771a045

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_EntropyBarrier
import Theorems.Thm_FirstPassageLinearTransport_barrierHitCount_mul_cosh_le
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (a θ : ℝ) (M : ℕ) (ha : 0 ≤ a) (hθ : 0 ≤ θ) :
    (barrierHitCount a M 0 : ℝ) ≤
      (2 : ℝ) ^ (M + 1) *
        Real.exp ((M : ℝ) * Real.log (Real.cosh θ) - θ * a) := by
  have hpot := barrierHitCount_mul_cosh_le a θ M 0 ha hθ
  have hlower : Real.exp (θ * a) / 2 ≤ Real.cosh (θ * a) := by
    rw [Real.cosh_eq]
    nlinarith [Real.exp_pos (-(θ * a))]
  have hleft :
      (barrierHitCount a M 0 : ℝ) * (Real.exp (θ * a) / 2) ≤
        (barrierHitCount a M 0 : ℝ) * Real.cosh (θ * a) :=
    mul_le_mul_of_nonneg_left hlower (by positivity)
  have hcoshpow :
      Real.cosh θ ^ M =
        Real.exp ((M : ℝ) * Real.log (Real.cosh θ)) := by
    calc
      Real.cosh θ ^ M =
          Real.exp (Real.log (Real.cosh θ)) ^ M := by
        rw [Real.exp_log (Real.cosh_pos θ)]
      _ = Real.exp ((M : ℝ) * Real.log (Real.cosh θ)) := by
        rw [← Real.exp_nat_mul]
  have hmain :
      (barrierHitCount a M 0 : ℝ) * Real.exp (θ * a) ≤
        2 * ((2 : ℝ) ^ M *
          Real.exp ((M : ℝ) * Real.log (Real.cosh θ))) := by
    have hhalf :
        (barrierHitCount a M 0 : ℝ) * (Real.exp (θ * a) / 2) ≤
          (2 : ℝ) ^ M * Real.cosh θ ^ M := by
      calc
        _ ≤ (barrierHitCount a M 0 : ℝ) * Real.cosh (θ * a) := hleft
        _ ≤ (2 : ℝ) ^ M * Real.cosh (θ * (0 : ℝ)) *
            Real.cosh θ ^ M := by
          simpa only [Int.cast_zero] using hpot
        _ = (2 : ℝ) ^ M * Real.cosh θ ^ M := by norm_num
    rw [hcoshpow] at hhalf
    nlinarith
  have hdiv :
      (barrierHitCount a M 0 : ℝ) ≤
        (2 * ((2 : ℝ) ^ M *
          Real.exp ((M : ℝ) * Real.log (Real.cosh θ)))) /
            Real.exp (θ * a) :=
    (le_div_iff₀ (Real.exp_pos (θ * a))).2 (by
      simpa [mul_comm] using hmain)
  calc
    (barrierHitCount a M 0 : ℝ) ≤
        (2 * ((2 : ℝ) ^ M *
          Real.exp ((M : ℝ) * Real.log (Real.cosh θ)))) /
            Real.exp (θ * a) := hdiv
    _ = (2 : ℝ) ^ (M + 1) *
        Real.exp ((M : ℝ) * Real.log (Real.cosh θ) - θ * a) := by
      rw [Real.exp_sub, pow_succ]
      ring
end FirstPassageLinearTransport
