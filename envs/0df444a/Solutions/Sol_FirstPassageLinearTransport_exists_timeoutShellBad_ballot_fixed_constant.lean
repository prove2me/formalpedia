-- Prove2me | solution 1 for FirstPassageLinearTransport.exists_timeoutShellBad_ballot_fixed_constant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:10:25.82867+00:00
-- url     : https://prove2.me/submissions/cad9e19f-c484-4e69-85b5-8a31a86151d9

import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Theorems.Thm_FirstPassageLinearTransport_exists_timeoutShellBad_ballot_ratio_le
import Theorems.Thm_FirstPassageLinearTransport_collatzFairTiltRate_eq_firstPassageEndpointRate
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_stoppedBallotValue_cons
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_cons
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_scale
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.bootstrapC_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapD_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapSet_zero
attribute [local simp] FirstPassageLinearTransport.card_boolSupport_cons
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero
attribute [local simp] FirstPassageLinearTransport.stageClock_zero
attribute [local simp] FirstPassageLinearTransport.stageOrbit_zero
attribute [local simp] FirstPassageLinearTransport.stoppedBallotValue_cons



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (K₀ C : ℝ) (hK₀ : 0 ≤ K₀) (hC : 0 ≤ C) :
    ∃ D : ℝ, 0 < D ∧
      ∀ L m : ℕ,
        0 < L → L ≤ m → (m : ℝ) ≤ C * (L : ℝ) →
        timeoutTargetRank K₀ L m ≤ m → 8 ≤ m →
        ((timeoutShellBad K₀ L m).card : ℝ) / (2 : ℝ) ^ m ≤
          D / ((m : ℝ) * Real.sqrt m) *
            Real.exp (-(firstPassageEndpointRate * (m : ℝ))) := by
  obtain ⟨C₀, hC₀, hRaw⟩ := exists_timeoutShellBad_ballot_ratio_le
  let B := (C * K₀ / 2 + 3) * Real.log 2
  let D := C₀ * (B + 1) * Real.exp (collatzTiltLambda * B)
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hD : 0 < D := by
    dsimp [D]
    positivity
  refine ⟨D, hD, ?_⟩
  intro L m hL hLm hmC hq hm
  have hbound := hRaw K₀ C L m hK₀ hC hL hLm hmC hq hm
  rw [collatzFairTiltRate_eq_firstPassageEndpointRate] at hbound
  calc
    ((timeoutShellBad K₀ L m).card : ℝ) / (2 : ℝ) ^ m ≤
        C₀ * (B + 1) / ((m : ℝ) * Real.sqrt m) *
          Real.exp (-(firstPassageEndpointRate * (m : ℝ)) +
            collatzTiltLambda * B) := by simpa [B] using hbound
    _ = D / ((m : ℝ) * Real.sqrt m) *
          Real.exp (-(firstPassageEndpointRate * (m : ℝ))) := by
      rw [show -(firstPassageEndpointRate * (m : ℝ)) +
          collatzTiltLambda * B =
          collatzTiltLambda * B +
            -(firstPassageEndpointRate * (m : ℝ)) by ring,
        Real.exp_add]
      dsimp [D]
      ring
end FirstPassageLinearTransport
