-- Prove2me | solution 1 for FirstPassageLinearTransport.barrierHitCount_le_chernoff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:23:36.584642+00:00
-- url     : https://prove2.me/submissions/f35021af-f066-4517-aea6-d2fdac2d3ab0

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_Density
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Theorems.Thm_FirstPassageLinearTransport_barrierHitCount_mul_cosh_le
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
open scoped BigOperators
namespace FirstPassageLinearTransport
theorem _root_.solution
    (a θ : ℝ) (r : ℕ) (ha : 0 ≤ a) (hθ : 0 ≤ θ) :
    (barrierHitCount a r 0 : ℝ) ≤
      (2 : ℝ) ^ (r + 1) *
        Real.exp (((r : ℝ) * θ ^ 2 / 2) - θ * a) := by
  have hpot := barrierHitCount_mul_cosh_le a θ r 0 ha hθ
  have hlower : Real.exp (θ * a) / 2 ≤ Real.cosh (θ * a) := by
    rw [Real.cosh_eq]
    nlinarith [Real.exp_pos (-(θ * a))]
  have hleft :
      (barrierHitCount a r 0 : ℝ) * (Real.exp (θ * a) / 2) ≤
        (barrierHitCount a r 0 : ℝ) * Real.cosh (θ * a) :=
    mul_le_mul_of_nonneg_left hlower (by positivity)
  have hcoshpow :
      Real.cosh θ ^ r ≤ Real.exp ((r : ℝ) * (θ ^ 2 / 2)) := by
    calc
      Real.cosh θ ^ r ≤ Real.exp (θ ^ 2 / 2) ^ r :=
        pow_le_pow_left₀ (Real.cosh_pos θ).le
          (Real.cosh_le_exp_half_sq θ) r
      _ = Real.exp ((r : ℝ) * (θ ^ 2 / 2)) := by
        rw [← Real.exp_nat_mul]
  have hmain :
      (barrierHitCount a r 0 : ℝ) * (Real.exp (θ * a) / 2) ≤
        (2 : ℝ) ^ r * Real.exp ((r : ℝ) * (θ ^ 2 / 2)) := by
    calc
      _ ≤ (barrierHitCount a r 0 : ℝ) * Real.cosh (θ * a) := hleft
      _ ≤ (2 : ℝ) ^ r * Real.cosh (θ * (0 : ℝ)) * Real.cosh θ ^ r := by
        simpa only [Int.cast_zero] using hpot
      _ = (2 : ℝ) ^ r * Real.cosh θ ^ r := by norm_num
      _ ≤ (2 : ℝ) ^ r * Real.exp ((r : ℝ) * (θ ^ 2 / 2)) :=
        mul_le_mul_of_nonneg_left hcoshpow (by positivity)
  have hmul :
      (barrierHitCount a r 0 : ℝ) * Real.exp (θ * a) ≤
        2 * ((2 : ℝ) ^ r * Real.exp ((r : ℝ) * (θ ^ 2 / 2))) := by
    nlinarith
  have hdiv :
      (barrierHitCount a r 0 : ℝ) ≤
        (2 * ((2 : ℝ) ^ r * Real.exp ((r : ℝ) * (θ ^ 2 / 2)))) /
          Real.exp (θ * a) :=
    (le_div_iff₀ (Real.exp_pos (θ * a))).2 (by simpa [mul_comm] using hmul)
  calc
    (barrierHitCount a r 0 : ℝ) ≤
        (2 * ((2 : ℝ) ^ r * Real.exp ((r : ℝ) * (θ ^ 2 / 2)))) /
          Real.exp (θ * a) := hdiv
    _ = (2 : ℝ) ^ (r + 1) *
          Real.exp (((r : ℝ) * θ ^ 2 / 2) - θ * a) := by
      rw [Real.exp_sub]
      ring
end FirstPassageLinearTransport
