-- Prove2me | solution 1 for FirstPassageLinearTransport.stoppedUpperMass_mean_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:52:11.600384+00:00
-- url     : https://prove2.me/submissions/7a230bc0-6b05-440c-95bb-6790810ce32d

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
    {x : Bool → ℝ} (hx : ∀ b, |x b| ≤ 1) {lo hi : ℝ}
    (hlohi : lo ≤ hi) :
    ∀ r z, lo - 1 ≤ z →
      (lo - 1) * (1 - stoppedUpperMass p x lo hi r z) +
          hi * stoppedUpperMass p x lo hi r z ≤
        stoppedWalkMean p x lo hi r z := by
  intro r
  induction r with
  | zero =>
      intro z hzlo
      by_cases hup : hi ≤ z
      · simp [stoppedUpperMass, stoppedWalkMean, hup]
      · simp [stoppedUpperMass, stoppedWalkMean, hup, hzlo]
  | succ r ihr =>
      intro z hzlo
      by_cases hup : hi ≤ z
      · have hnotlo : ¬z < lo := by
          intro hz
          linarith
        simp [stoppedUpperMass, stoppedWalkMean, hup, hnotlo]
      · by_cases hlo : z < lo
        · have hstop : z < lo ∨ hi ≤ z := Or.inl hlo
          simp [stoppedUpperMass, stoppedWalkMean, hup, hlo, hstop, hzlo]
        · have hstop : ¬(z < lo ∨ hi ≤ z) := not_or_intro hlo hup
          have hxFalse := abs_le.mp (hx false)
          have hxTrue := abs_le.mp (hx true)
          have hf := ihr (z + x false) (by linarith)
          have ht := ihr (z + x true) (by linarith)
          simp only [stoppedUpperMass, stoppedWalkMean, hup, hlo, hstop, if_false]
          have havg := bernoulliAverage_mono hp₀ hp₁ hf ht
          calc
            (lo - 1) *
                  (1 - bernoulliAverage p
                    (stoppedUpperMass p x lo hi r (z + x false))
                    (stoppedUpperMass p x lo hi r (z + x true))) +
                hi * bernoulliAverage p
                  (stoppedUpperMass p x lo hi r (z + x false))
                  (stoppedUpperMass p x lo hi r (z + x true)) =
              bernoulliAverage p
                ((lo - 1) *
                    (1 - stoppedUpperMass p x lo hi r (z + x false)) +
                  hi * stoppedUpperMass p x lo hi r (z + x false))
                ((lo - 1) *
                    (1 - stoppedUpperMass p x lo hi r (z + x true)) +
                  hi * stoppedUpperMass p x lo hi r (z + x true)) := by
                unfold bernoulliAverage
                ring
            _ ≤ bernoulliAverage p
                (stoppedWalkMean p x lo hi r (z + x false))
                (stoppedWalkMean p x lo hi r (z + x true)) := havg
end FirstPassageLinearTransport
