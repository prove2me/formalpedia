-- Prove2me | solution 1 for FirstPassageLinearTransport.stoppedHorizonMass_mul_le_time
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:52:12.470177+00:00
-- url     : https://prove2.me/submissions/a3b9d37b-b175-45d2-8994-3411da242abb

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_bernoulliAverage_le_one
import Theorems.Thm_FirstPassageLinearTransport_bernoulliAverage_mono
import Theorems.Thm_FirstPassageLinearTransport_stoppedHorizonMass_mem_unit
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
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (x : Bool → ℝ) (lo hi : ℝ) :
    ∀ (r : ℕ) (z : ℝ), (r : ℝ) * stoppedHorizonMass p x lo hi r z ≤
      stoppedWalkTime p x lo hi r z := by
  intro r
  induction r with
  | zero => simp [stoppedHorizonMass, stoppedWalkTime]
  | succ r ihr =>
      intro z
      by_cases hstop : z < lo ∨ hi ≤ z
      · simp [stoppedHorizonMass, stoppedWalkTime, hstop]
      · have hf := ihr (z + x false)
        have ht := ihr (z + x true)
        have havg := bernoulliAverage_mono hp₀ hp₁ hf ht
        have hmass := stoppedHorizonMass_mem_unit hp₀ hp₁ x lo hi
        have hunit := bernoulliAverage_le_one hp₀ hp₁
          (hmass r (z + x false)).2 (hmass r (z + x true)).2
        simp only [stoppedHorizonMass, stoppedWalkTime, hstop, if_false,
          Nat.cast_add, Nat.cast_one]
        unfold bernoulliAverage at havg hunit ⊢
        nlinarith
end FirstPassageLinearTransport
