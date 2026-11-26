-- Prove2me | solution 1 for FirstPassageLinearTransport.exists_sum_collatzQuarterSplitFairBinMass_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:01:33.129235+00:00
-- url     : https://prove2.me/submissions/d792f408-9854-4762-a406-f408cbbb3074

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_exists_sum_collatzThreeBlockFairBinMass_le
import Theorems.Thm_FirstPassageLinearTransport_collatzBallot_split
import Theorems.Thm_FirstPassageLinearTransport_collatzBallotOuterLength_pos
import Theorems.Thm_FirstPassageLinearTransport_collatzBallotMiddleLength_pos
import Theorems.Thm_FirstPassageLinearTransport_collatzBallot_denominator_lower
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
theorem _root_.solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ m Q : ℕ, ∀ B : ℝ,
        8 ≤ m → 0 ≤ B →
          ∑ q ∈ Finset.range Q,
              collatzThreeBlockFlatMass (1 / 2)
                (collatzBallotOuterLength m)
                (collatzBallotMiddleLength m) B q ≤
            C * (B + 1) / ((m : ℝ) * Real.sqrt m) *
              Real.exp (-(collatzFairTiltRate * (m : ℝ)) +
                collatzTiltLambda * B) := by
  obtain ⟨C₀, hC₀, hbase⟩ := exists_sum_collatzThreeBlockFairBinMass_le
  refine ⟨16 * C₀, by positivity, ?_⟩
  intro m Q B hm hB
  have ha : 0 < collatzBallotOuterLength m :=
    collatzBallotOuterLength_pos hm
  have hb : 0 < collatzBallotMiddleLength m :=
    collatzBallotMiddleLength_pos hm
  have hraw := hbase (collatzBallotOuterLength m)
    (collatzBallotMiddleLength m) Q B ha hb hB
  let D : ℝ := Real.sqrt (collatzBallotOuterLength m) *
    Real.sqrt (collatzBallotOuterLength m) *
      Real.sqrt (collatzBallotMiddleLength m)
  let d₀ : ℝ := (m : ℝ) * Real.sqrt m / 16
  let N : ℝ := C₀ * (B + 1)
  let E : ℝ := Real.exp (-(collatzFairTiltRate * (m : ℝ)) +
    collatzTiltLambda * B)
  have hD : d₀ ≤ D := collatzBallot_denominator_lower hm
  have hd₀ : 0 < d₀ := by
    dsimp [d₀]
    positivity
  have hN : 0 ≤ N := by
    dsimp [N]
    positivity
  have hfrac : N / D ≤ N / d₀ :=
    div_le_div_of_nonneg_left hN hd₀ hD
  have hlen : 2 * collatzBallotOuterLength m +
      collatzBallotMiddleLength m = m := collatzBallot_split m
  have hexp :
      Real.exp (-(collatzFairTiltRate *
          ((2 * collatzBallotOuterLength m +
            collatzBallotMiddleLength m : ℕ) : ℝ)) +
          collatzTiltLambda * B) = E := by
    rw [hlen]
  rw [hexp] at hraw
  calc
    (∑ q ∈ Finset.range Q,
        collatzThreeBlockFlatMass (1 / 2)
          (collatzBallotOuterLength m)
          (collatzBallotMiddleLength m) B q) ≤ N / D * E := by
      simpa [N, D] using hraw
    _ ≤ N / d₀ * E :=
      mul_le_mul_of_nonneg_right hfrac (Real.exp_pos _).le
    _ = (16 * C₀) * (B + 1) / ((m : ℝ) * Real.sqrt m) *
        Real.exp (-(collatzFairTiltRate * (m : ℝ)) +
          collatzTiltLambda * B) := by
      dsimp [N, d₀, E]
      field_simp
      <;> ring
end FirstPassageLinearTransport
