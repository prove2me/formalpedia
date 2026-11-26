-- Prove2me | solution 1 for FirstPassageLinearTransport.stoppedWalkMoment_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:52:04.584792+00:00
-- url     : https://prove2.me/submissions/75a7f31c-5afc-4087-98e1-32def53387d3

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_bernoulliAverage_mono
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
    {x : Bool → ℝ} (hx : ∀ b, |x b| ≤ 1) {lo hi : ℝ} :
    ∀ r z, lo - 1 ≤ z → z ≤ hi + 1 →
      stoppedWalkSecond p x lo hi r z ≤
        (lo + hi) * stoppedWalkMean p x lo hi r z -
          (lo - 1) * (hi + 1) := by
  intro r
  induction r with
  | zero =>
      intro z hzlo hzhi
      simp only [stoppedWalkSecond, stoppedWalkMean]
      have hprod : 0 ≤ (z - (lo - 1)) * ((hi + 1) - z) :=
        mul_nonneg (sub_nonneg.mpr hzlo) (sub_nonneg.mpr hzhi)
      nlinarith
  | succ r ihr =>
      intro z hzlo hzhi
      by_cases hstop : z < lo ∨ hi ≤ z
      · simp only [stoppedWalkSecond, stoppedWalkMean, hstop, if_true]
        have hprod : 0 ≤ (z - (lo - 1)) * ((hi + 1) - z) :=
          mul_nonneg (sub_nonneg.mpr hzlo) (sub_nonneg.mpr hzhi)
        nlinarith
      · have hzSafe : lo ≤ z ∧ z < hi := by
          constructor
          · exact le_of_not_gt (fun h => hstop (Or.inl h))
          · exact lt_of_not_ge (fun h => hstop (Or.inr h))
        have hxFalse := abs_le.mp (hx false)
        have hxTrue := abs_le.mp (hx true)
        have hf := ihr (z + x false) (by linarith) (by linarith)
        have ht := ihr (z + x true) (by linarith) (by linarith)
        simp only [stoppedWalkSecond, stoppedWalkMean, hstop, if_false]
        have havg := bernoulliAverage_mono hp₀ hp₁ hf ht
        unfold bernoulliAverage at havg ⊢
        nlinarith
end FirstPassageLinearTransport
