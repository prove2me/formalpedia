-- Prove2me | solution 1 for FirstPassageLinearTransport.barrierHitCount_mul_cosh_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:22:49.609071+00:00
-- url     : https://prove2.me/submissions/ed8cf237-0e71-4a56-989a-efde4f9c5555

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_Density
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Theorems.Thm_FirstPassageLinearTransport_barrierHitCount_of_bad
import Theorems.Thm_FirstPassageLinearTransport_barrierHitCount_succ_of_safe
import Theorems.Thm_FirstPassageLinearTransport_cosh_int_children
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


section
namespace FirstPassageLinearTransport
open scoped BigOperators
private theorem cosh_barrier_le_position {a θ : ℝ} {y : ℤ}
    (ha : 0 ≤ a) (hθ : 0 ≤ θ) (hy : a < |(y : ℝ)|) :
    Real.cosh (θ * a) ≤ Real.cosh (θ * (y : ℝ)) := by
  rw [Real.cosh_le_cosh]
  rw [abs_mul, abs_mul, abs_of_nonneg hθ, abs_of_nonneg ha]
  exact mul_le_mul_of_nonneg_left (le_of_lt hy) hθ
end FirstPassageLinearTransport
end

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
namespace FirstPassageLinearTransport
theorem _root_.solution
    (a θ : ℝ) (r : ℕ) (y : ℤ) (ha : 0 ≤ a) (hθ : 0 ≤ θ) :
    (barrierHitCount a r y : ℝ) * Real.cosh (θ * a) ≤
      (2 : ℝ) ^ r * Real.cosh (θ * (y : ℝ)) * Real.cosh θ ^ r := by
  induction r generalizing y with
  | zero =>
      by_cases hy : a < |(y : ℝ)|
      · rw [barrierHitCount_of_bad hy]
        simp only [pow_zero, Nat.cast_one, one_mul, mul_one]
        exact cosh_barrier_le_position ha hθ hy
      · simp [barrierHitCount, hitsBarrierFrom, hy, (Real.cosh_pos _).le]
  | succ r ihr =>
      by_cases hy : a < |(y : ℝ)|
      · rw [barrierHitCount_of_bad hy]
        have hcosh := cosh_barrier_le_position ha hθ hy
        have hpow : (1 : ℝ) ≤ Real.cosh θ ^ (r + 1) :=
          one_le_pow₀ (Real.one_le_cosh θ)
        have hcast : (((2 ^ (r + 1) : ℕ) : ℝ)) = (2 : ℝ) ^ (r + 1) := by
          norm_num
        calc
          ((2 ^ (r + 1) : ℕ) : ℝ) * Real.cosh (θ * a)
              ≤ (2 : ℝ) ^ (r + 1) * Real.cosh (θ * (y : ℝ)) := by
                rw [hcast]
                exact mul_le_mul_of_nonneg_left hcosh (by positivity)
          _ ≤ (2 : ℝ) ^ (r + 1) * Real.cosh (θ * (y : ℝ)) *
                Real.cosh θ ^ (r + 1) := by
              have hnonneg :
                  0 ≤ (2 : ℝ) ^ (r + 1) * Real.cosh (θ * (y : ℝ)) := by
                positivity
              simpa only [mul_one] using
                mul_le_mul_of_nonneg_left hpow hnonneg
      · rw [barrierHitCount_succ_of_safe hy]
        push_cast
        have hminus := ihr (y := y - 1)
        have hplus := ihr (y := y + 1)
        calc
          ((barrierHitCount a r (y - 1) : ℝ) +
                (barrierHitCount a r (y + 1) : ℝ)) * Real.cosh (θ * a) =
              (barrierHitCount a r (y - 1) : ℝ) * Real.cosh (θ * a) +
                (barrierHitCount a r (y + 1) : ℝ) * Real.cosh (θ * a) := by
                  ring
          _ ≤ (2 : ℝ) ^ r * Real.cosh (θ * ((y - 1 : ℤ) : ℝ)) *
                  Real.cosh θ ^ r +
                (2 : ℝ) ^ r * Real.cosh (θ * ((y + 1 : ℤ) : ℝ)) *
                  Real.cosh θ ^ r := add_le_add hminus hplus
          _ = (2 : ℝ) ^ (r + 1) * Real.cosh (θ * (y : ℝ)) *
                Real.cosh θ ^ (r + 1) := by
              calc
                _ = (2 : ℝ) ^ r *
                      (Real.cosh (θ * ((y - 1 : ℤ) : ℝ)) +
                        Real.cosh (θ * ((y + 1 : ℤ) : ℝ))) *
                      Real.cosh θ ^ r := by ring
                _ = (2 : ℝ) ^ r *
                      (2 * Real.cosh (θ * (y : ℝ)) * Real.cosh θ) *
                      Real.cosh θ ^ r := by rw [cosh_int_children]
                _ = _ := by rw [pow_succ, pow_succ]; ring
end FirstPassageLinearTransport
