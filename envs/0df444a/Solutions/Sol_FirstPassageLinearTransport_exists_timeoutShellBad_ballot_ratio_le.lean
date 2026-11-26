-- Prove2me | solution 1 for FirstPassageLinearTransport.exists_timeoutShellBad_ballot_ratio_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:08:55.588797+00:00
-- url     : https://prove2.me/submissions/52615bd4-86c3-4913-9a9d-6f1dc30a1d44

import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Theorems.Thm_FirstPassageLinearTransport_collatzSurvivalMass_le_fullWordBins
import Theorems.Thm_FirstPassageLinearTransport_weightedSurvivalWordMass_half_eq_card
import Theorems.Thm_FirstPassageLinearTransport_card_collatzSurvivalShell
import Theorems.Thm_FirstPassageLinearTransport_timeoutShellBad_subset_collatzSurvivalShell
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_exists_sum_collatzQuarterSplitFullWordMass_le
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
theorem _root_.solution :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ K₀ C : ℝ, ∀ L m : ℕ,
        0 ≤ K₀ → 0 ≤ C → 0 < L → L ≤ m →
        (m : ℝ) ≤ C * (L : ℝ) →
        timeoutTargetRank K₀ L m ≤ m → 8 ≤ m →
        ((timeoutShellBad K₀ L m).card : ℝ) / (2 : ℝ) ^ m ≤
          C₀ * (((C * K₀ / 2 + 3) * Real.log 2) + 1) /
              ((m : ℝ) * Real.sqrt m) *
            Real.exp (-(collatzFairTiltRate * (m : ℝ)) +
              collatzTiltLambda * ((C * K₀ / 2 + 3) * Real.log 2)) := by
  obtain ⟨C₀, hC₀, hBallot⟩ :=
    exists_sum_collatzQuarterSplitFullWordMass_le
  refine ⟨C₀, hC₀, ?_⟩
  intro K₀ C L m hK₀ hC hL _hLm hmC hq hm
  let B := (C * K₀ / 2 + 3) * Real.log 2
  let Q := m + ⌈B⌉₊ + 2
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hsubset := timeoutShellBad_subset_collatzSurvivalShell
    hK₀ hL hmC hq
  have hcard : (timeoutShellBad K₀ L m).card ≤
      (collatzSurvivalShell m B).card := by
    exact Finset.card_le_card hsubset
  have hcardR : ((timeoutShellBad K₀ L m).card : ℝ) ≤
      (collatzSurvivalShell m B).card := by exact_mod_cast hcard
  have hpow : 0 < (2 : ℝ) ^ m := by positivity
  calc
    ((timeoutShellBad K₀ L m).card : ℝ) / (2 : ℝ) ^ m ≤
        ((collatzSurvivalShell m B).card : ℝ) / (2 : ℝ) ^ m := by
      exact div_le_div_of_nonneg_right hcardR hpow.le
    _ = weightedSurvivalWordMass (1 / 2) collatzLogIncrement (-B) m 0 := by
      rw [card_collatzSurvivalShell,
        weightedSurvivalWordMass_half_eq_card]
    _ ≤ ∑ q ∈ Finset.range Q,
        collatzFullWordMass (1 / 2) m B (q : ℝ) := by
      exact collatzSurvivalMass_le_fullWordBins (le_refl Q)
    _ ≤ C₀ * (B + 1) / ((m : ℝ) * Real.sqrt m) *
          Real.exp (-(collatzFairTiltRate * (m : ℝ)) +
            collatzTiltLambda * B) := hBallot m Q B hm hB
    _ = C₀ * (((C * K₀ / 2 + 3) * Real.log 2) + 1) /
              ((m : ℝ) * Real.sqrt m) *
            Real.exp (-(collatzFairTiltRate * (m : ℝ)) +
              collatzTiltLambda * ((C * K₀ / 2 + 3) * Real.log 2)) := by
      rfl
end FirstPassageLinearTransport
