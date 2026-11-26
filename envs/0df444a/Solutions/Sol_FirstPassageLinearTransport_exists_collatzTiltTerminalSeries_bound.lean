-- Prove2me | solution 1 for FirstPassageLinearTransport.exists_collatzTiltTerminalSeries_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:55:51.924586+00:00
-- url     : https://prove2.me/submissions/68c97ca0-905d-4421-a197-e2dac7d32b2e

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_collatzTiltLambda_pos
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
    ∃ S : ℝ, 0 < S ∧ ∀ Q : ℕ,
      ∑ q ∈ Finset.range Q,
          ((q : ℝ) + 2) *
            Real.exp (-collatzTiltLambda * (q : ℝ)) ≤ S := by
  have hsum1 : Summable (fun q : ℕ ↦
      (q : ℝ) * Real.exp (-collatzTiltLambda * (q : ℝ))) := by
    simpa [mul_comm] using
      (Real.summable_pow_mul_exp_neg_nat_mul 1 collatzTiltLambda_pos)
  have hsum0 : Summable (fun q : ℕ ↦
      Real.exp (-collatzTiltLambda * (q : ℝ))) := by
    simpa using
      (Real.summable_pow_mul_exp_neg_nat_mul 0 collatzTiltLambda_pos)
  have hsum : Summable (fun q : ℕ ↦
      ((q : ℝ) + 2) *
        Real.exp (-collatzTiltLambda * (q : ℝ))) := by
    convert hsum1.add (hsum0.mul_left 2) using 1
    funext q
    ring
  let S := 1 + ∑' q : ℕ,
    ((q : ℝ) + 2) * Real.exp (-collatzTiltLambda * (q : ℝ))
  have htsum : 0 ≤ ∑' q : ℕ,
      ((q : ℝ) + 2) * Real.exp (-collatzTiltLambda * (q : ℝ)) := by
    exact tsum_nonneg fun q ↦
      mul_nonneg (by positivity) (Real.exp_pos _).le
  refine ⟨S, by dsimp [S]; linarith, ?_⟩
  intro Q
  have hpartial :
      ∑ q ∈ Finset.range Q,
          ((q : ℝ) + 2) *
            Real.exp (-collatzTiltLambda * (q : ℝ)) ≤
        ∑' q : ℕ,
          ((q : ℝ) + 2) *
            Real.exp (-collatzTiltLambda * (q : ℝ)) := by
    exact hsum.sum_le_tsum (Finset.range Q)
      (fun q _hq ↦ mul_nonneg (by positivity) (Real.exp_pos _).le)
  dsimp [S]
  linarith
end FirstPassageLinearTransport
