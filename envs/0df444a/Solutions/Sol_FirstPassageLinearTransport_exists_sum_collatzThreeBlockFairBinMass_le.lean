-- Prove2me | solution 1 for FirstPassageLinearTransport.exists_sum_collatzThreeBlockFairBinMass_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:00:45.641794+00:00
-- url     : https://prove2.me/submissions/3a411e61-4cec-41d0-983a-a3c77a9b19b4

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_exists_collatzTiltTerminalSeries_bound
import Theorems.Thm_FirstPassageLinearTransport_exists_collatzThreeBlockFairBinMass_le
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
      ∀ a b Q : ℕ, ∀ B : ℝ,
        0 < a → 0 < b → 0 ≤ B →
          ∑ q ∈ Finset.range Q,
              collatzThreeBlockFlatMass (1 / 2) a b B q ≤
            C * (B + 1) /
                (Real.sqrt a * Real.sqrt a * Real.sqrt b) *
              Real.exp (-(collatzFairTiltRate *
                ((2 * a + b : ℕ) : ℝ)) + collatzTiltLambda * B) := by
  obtain ⟨C₀, hC₀, hBin⟩ := exists_collatzThreeBlockFairBinMass_le
  obtain ⟨S, hS, hSeries⟩ := exists_collatzTiltTerminalSeries_bound
  refine ⟨C₀ * S, mul_pos hC₀ hS, ?_⟩
  intro a b Q B ha hb hB
  let D : ℝ := Real.sqrt a * Real.sqrt a * Real.sqrt b
  let K : ℝ := C₀ * (B + 1) / D *
    Real.exp (-(collatzFairTiltRate * ((2 * a + b : ℕ) : ℝ)) +
      collatzTiltLambda * B)
  have hD : 0 < D := by
    dsimp [D]
    exact mul_pos
      (mul_pos (Real.sqrt_pos.2 (by positivity))
        (Real.sqrt_pos.2 (by positivity)))
      (Real.sqrt_pos.2 (by positivity))
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hpoint : ∀ q ∈ Finset.range Q,
      collatzThreeBlockFlatMass (1 / 2) a b B q ≤
        K * (((q : ℝ) + 2) *
          Real.exp (-collatzTiltLambda * (q : ℝ))) := by
    intro q _hq
    have hq : 0 ≤ (q : ℝ) := by positivity
    have hqBin := hBin a b B (q : ℝ) ha hb hB hq
    have hexp :
        Real.exp (-(collatzFairTiltRate * ((2 * a + b : ℕ) : ℝ)) -
            collatzTiltLambda * ((q : ℝ) - B)) =
          Real.exp (-(collatzFairTiltRate * ((2 * a + b : ℕ) : ℝ)) +
              collatzTiltLambda * B) *
            Real.exp (-collatzTiltLambda * (q : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp] at hqBin
    dsimp [K, D]
    calc
      collatzThreeBlockFlatMass (1 / 2) a b B (q : ℝ) ≤
          C₀ * (B + 1) * ((q : ℝ) + 2) /
              (Real.sqrt a * Real.sqrt a * Real.sqrt b) *
            (Real.exp (-(collatzFairTiltRate *
                ((2 * a + b : ℕ) : ℝ)) + collatzTiltLambda * B) *
              Real.exp (-collatzTiltLambda * (q : ℝ))) := hqBin
      _ = (C₀ * (B + 1) /
              (Real.sqrt a * Real.sqrt a * Real.sqrt b) *
            Real.exp (-(collatzFairTiltRate *
                ((2 * a + b : ℕ) : ℝ)) + collatzTiltLambda * B)) *
          (((q : ℝ) + 2) *
            Real.exp (-collatzTiltLambda * (q : ℝ))) := by ring
  calc
    (∑ q ∈ Finset.range Q,
        collatzThreeBlockFlatMass (1 / 2) a b B q) ≤
        ∑ q ∈ Finset.range Q,
          K * (((q : ℝ) + 2) *
            Real.exp (-collatzTiltLambda * (q : ℝ))) :=
      Finset.sum_le_sum hpoint
    _ = K * (∑ q ∈ Finset.range Q,
          ((q : ℝ) + 2) *
            Real.exp (-collatzTiltLambda * (q : ℝ))) := by
      rw [Finset.mul_sum]
    _ ≤ K * S := mul_le_mul_of_nonneg_left (hSeries Q) hK
    _ = (C₀ * S) * (B + 1) /
          (Real.sqrt a * Real.sqrt a * Real.sqrt b) *
        Real.exp (-(collatzFairTiltRate *
          ((2 * a + b : ℕ) : ℝ)) + collatzTiltLambda * B) := by
      dsimp [K, D]
      ring
end FirstPassageLinearTransport
