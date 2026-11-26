-- Prove2me | solution 1 for FirstPassageLinearTransport.timeoutStrengthenedEndpointNaturalDensityDescentOfPackage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:38:12.647214+00:00
-- url     : https://prove2.me/submissions/33b19820-5890-451e-9d97-7a40e3688a80

import Definitions.Def_FirstPassageLinearTransport_MovingEndpointAssembly
import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointAsymptotics
import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointWitness
import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointNaturalDensity
import Theorems.Thm_FirstPassageLinearTransport_StageSetup_lowerTolerance_M0
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_driftGap_pos
import Theorems.Thm_FirstPassageLinearTransport_eventually_timeoutStrengthenedEndpointGood_has_shellWitness
import Theorems.Thm_FirstPassageLinearTransport_exists_eventually_timeoutStrengthenedEndpointGood_sharpShellError
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell_log
import Theorems.Thm_FirstPassageLinearTransport_mem_firstBadLandingEnvelope
import Theorems.Thm_FirstPassageLinearTransport_mem_generatedFirstBadSources
import Theorems.Thm_FirstPassageLinearTransport_mem_landingBad
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTaggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTransportedSources
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTransportedSourcesAtTimes
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_shrinkingFeasibleTimes
import Theorems.Thm_FirstPassageLinearTransport_mem_shrinkingFirstBadSourcesAtRank
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_timeoutFirstBadSourcesAtRank
import Theorems.Thm_FirstPassageLinearTransport_mem_timeoutHighFirstBadSourcesAtRank
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_naturalDensityOne_of_sharpMovingShellErrorWithHeight
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawFirstPassageTime_self
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shellBad_assembleDyadic
import Theorems.Thm_FirstPassageLinearTransport_shellClock_le_natLog
import Theorems.Thm_FirstPassageLinearTransport_shortcutFirstPassageTime_self
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_shrinkingHighSetup_M0
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_stoppedBallotValue_cons
import Theorems.Thm_FirstPassageLinearTransport_tendsto_natLogTwo_atTop
attribute [local simp] FirstPassageLinearTransport.StageSetup.lowerTolerance_M0
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_cons
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_scale
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.bootstrapC_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapD_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapSet_zero
attribute [local simp] FirstPassageLinearTransport.card_boolSupport_cons
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_firstBadLandingEnvelope
attribute [local simp] FirstPassageLinearTransport.mem_generatedFirstBadSources
attribute [local simp] FirstPassageLinearTransport.mem_landingBad
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTaggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTransportedSources
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTransportedSourcesAtTimes
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.mem_shrinkingFeasibleTimes
attribute [local simp] FirstPassageLinearTransport.mem_shrinkingFirstBadSourcesAtRank
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_timeoutFirstBadSourcesAtRank
attribute [local simp] FirstPassageLinearTransport.mem_timeoutHighFirstBadSourcesAtRank
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.rawFirstPassageTime_self
attribute [local simp] FirstPassageLinearTransport.rawOrbit_zero
attribute [local simp] FirstPassageLinearTransport.shortcutFirstPassageTime_self
attribute [local simp] FirstPassageLinearTransport.shortcut_zero
attribute [local simp] FirstPassageLinearTransport.shrinkingHighSetup_M0
attribute [local simp] FirstPassageLinearTransport.stageClock_zero
attribute [local simp] FirstPassageLinearTransport.stageOrbit_zero
attribute [local simp] FirstPassageLinearTransport.stoppedBallotValue_cons



set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {A R : ℕ → ℝ} {Amax c beta : ℝ}
    (P : MovingEndpointParameterPackage Amax c beta)
    (hbuffer : Tendsto (sharpMovingRankBuffer A) atTop atTop)
    (hUpper : ∀ᶠ M : ℕ in atTop, A M ≤ Amax)
    (hR : Tendsto R atTop atTop) :
    ∃ S : Set ℕ, ∃ C : ℝ,
      0 < C ∧ NaturalDensityOne S ∧
      (∀ᶠ M : ℕ in atTop,
        shellExceptionalRatio S M ≤
          C * ((2 : ℝ) ^ (-(sharpMovingRankBuffer A M)) +
            (((M : ℝ) + 2) ^ (-P.epsilon))) + 4 / R M) ∧
      (∀ᶠ n : ℕ in atTop, n ∈ S →
        ∃ k ell : ℕ,
          (k : ℝ) < c * Real.log n ∧
          |driftGap * (k : ℝ) - (Nat.log 2 n : ℝ)| ≤
            C * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
              Real.log ((Nat.log 2 n : ℝ) + 2)) ∧
          |(2 * driftGap / 3) * (ell : ℝ) - (Nat.log 2 n : ℝ)| ≤
            C * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
              Real.log ((Nat.log 2 n : ℝ) + 2)) ∧
          (∀ j : ℕ, j ≤ k →
            |shortcutLogDeviation n j| ≤
              C * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
                Real.log ((Nat.log 2 n : ℝ) + 2))) ∧
          (∀ j : ℕ, j ≤ k →
            |(oddCount n j : ℝ) - (j : ℝ) / 2| ≤
              C * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
                Real.log ((Nat.log 2 n : ℝ) + 2))) ∧
          (∀ i : ℕ, i ≤ ell →
            |rawLogDeviation n i| ≤
              C * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
                Real.log ((Nat.log 2 n : ℝ) + 2))) ∧
          ell = rawTime n k ∧
          rawOrbit ell n = orbit k n ∧
          (orbit k n : ℝ) <
            C * (Real.log n) ^ (A (Nat.log 2 n)) ∧
          (∀ j : ℕ, j ≤ k →
            (orbit j n : ℝ) ≤
              (n : ℝ) * R (Nat.log 2 n) / 2) ∧
          (∀ i : ℕ, i ≤ ell →
            (rawOrbit i n : ℝ) ≤
              (n : ℝ) * R (Nat.log 2 n))) := by
  have hR4 : ∀ᶠ M : ℕ in atTop, 4 ≤ R M :=
    (tendsto_atTop.1 hR) 4
  obtain ⟨Cprof, hCprof, hProfile⟩ :=
    exists_eventually_timeoutStrengthenedEndpointGood_sharpShellError
      P hbuffer hUpper hR4
  let C := max
    (max
      (max Cprof (fixedPolylogTargetConstant Amax))
      (max
        (2 * timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch)
        (timeoutCompletedRawClockSupportConstant
          P.run.toTimeoutHigh P.Cswitch)))
    (max
      (timeoutCompletedOddTrajectorySupportConstant
        P.run.toTimeoutHigh P.Cswitch)
      (timeoutCompletedRawTrajectorySupportConstant
        P.run.toTimeoutHigh P.Cswitch)) + 1
  let S : Set ℕ := assembleDyadic (timeoutStrengthenedEndpointGood P A R)
  have hCprofC : Cprof ≤ C := by
    have h₁ : Cprof ≤ max Cprof (fixedPolylogTargetConstant Amax) :=
      le_max_left _ _
    have h₂ : max Cprof (fixedPolylogTargetConstant Amax) ≤
        max (max Cprof (fixedPolylogTargetConstant Amax))
          (max
            (2 * timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch)
            (timeoutCompletedRawClockSupportConstant
              P.run.toTimeoutHigh P.Cswitch)) :=
      le_max_left _ _
    have h₃ : max
          (max Cprof (fixedPolylogTargetConstant Amax))
          (max
            (2 * timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch)
            (timeoutCompletedRawClockSupportConstant
              P.run.toTimeoutHigh P.Cswitch)) ≤
        max
          (max
            (max Cprof (fixedPolylogTargetConstant Amax))
            (max
              (2 * timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch)
              (timeoutCompletedRawClockSupportConstant
                P.run.toTimeoutHigh P.Cswitch)))
          (max
            (timeoutCompletedOddTrajectorySupportConstant
              P.run.toTimeoutHigh P.Cswitch)
            (timeoutCompletedRawTrajectorySupportConstant
              P.run.toTimeoutHigh P.Cswitch)) := le_max_left _ _
    dsimp [C]
    linarith
  have hTargetC : fixedPolylogTargetConstant Amax ≤ C := by
    have h₁ : fixedPolylogTargetConstant Amax ≤
        max Cprof (fixedPolylogTargetConstant Amax) := le_max_right _ _
    have h₂ : max Cprof (fixedPolylogTargetConstant Amax) ≤
        max (max Cprof (fixedPolylogTargetConstant Amax))
          (max
            (2 * timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch)
            (timeoutCompletedRawClockSupportConstant
              P.run.toTimeoutHigh P.Cswitch)) :=
      le_max_left _ _
    have h₃ : max
          (max Cprof (fixedPolylogTargetConstant Amax))
          (max
            (2 * timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch)
            (timeoutCompletedRawClockSupportConstant
              P.run.toTimeoutHigh P.Cswitch)) ≤
        max
          (max
            (max Cprof (fixedPolylogTargetConstant Amax))
            (max
              (2 * timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch)
              (timeoutCompletedRawClockSupportConstant
                P.run.toTimeoutHigh P.Cswitch)))
          (max
            (timeoutCompletedOddTrajectorySupportConstant
              P.run.toTimeoutHigh P.Cswitch)
            (timeoutCompletedRawTrajectorySupportConstant
              P.run.toTimeoutHigh P.Cswitch)) := le_max_left _ _
    dsimp [C]
    linarith
  have hClockC :
      2 * timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch ≤ C := by
    have h₁ : 2 * timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch ≤
        max
          (2 * timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch)
          (timeoutCompletedRawClockSupportConstant
            P.run.toTimeoutHigh P.Cswitch) := le_max_left _ _
    have h₂ : max
          (2 * timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch)
          (timeoutCompletedRawClockSupportConstant
            P.run.toTimeoutHigh P.Cswitch) ≤
        max (max Cprof (fixedPolylogTargetConstant Amax))
          (max
            (2 * timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch)
            (timeoutCompletedRawClockSupportConstant
              P.run.toTimeoutHigh P.Cswitch)) := le_max_right _ _
    have h₃ : max
          (max Cprof (fixedPolylogTargetConstant Amax))
          (max
            (2 * timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch)
            (timeoutCompletedRawClockSupportConstant
              P.run.toTimeoutHigh P.Cswitch)) ≤
        max
          (max
            (max Cprof (fixedPolylogTargetConstant Amax))
            (max
              (2 * timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch)
              (timeoutCompletedRawClockSupportConstant
                P.run.toTimeoutHigh P.Cswitch)))
          (max
            (timeoutCompletedOddTrajectorySupportConstant
              P.run.toTimeoutHigh P.Cswitch)
            (timeoutCompletedRawTrajectorySupportConstant
              P.run.toTimeoutHigh P.Cswitch)) := le_max_left _ _
    dsimp [C]
    linarith
  have hRawClockC :
      timeoutCompletedRawClockSupportConstant
        P.run.toTimeoutHigh P.Cswitch ≤ C := by
    have h₁ : timeoutCompletedRawClockSupportConstant
          P.run.toTimeoutHigh P.Cswitch ≤
        max
          (2 * timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch)
          (timeoutCompletedRawClockSupportConstant
            P.run.toTimeoutHigh P.Cswitch) := le_max_right _ _
    have h₂ : max
          (2 * timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch)
          (timeoutCompletedRawClockSupportConstant
            P.run.toTimeoutHigh P.Cswitch) ≤
        max (max Cprof (fixedPolylogTargetConstant Amax))
          (max
            (2 * timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch)
            (timeoutCompletedRawClockSupportConstant
              P.run.toTimeoutHigh P.Cswitch)) := le_max_right _ _
    have h₃ : max
          (max Cprof (fixedPolylogTargetConstant Amax))
          (max
            (2 * timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch)
            (timeoutCompletedRawClockSupportConstant
              P.run.toTimeoutHigh P.Cswitch)) ≤
        max
          (max
            (max Cprof (fixedPolylogTargetConstant Amax))
            (max
              (2 * timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch)
              (timeoutCompletedRawClockSupportConstant
                P.run.toTimeoutHigh P.Cswitch)))
          (max
            (timeoutCompletedOddTrajectorySupportConstant
              P.run.toTimeoutHigh P.Cswitch)
            (timeoutCompletedRawTrajectorySupportConstant
              P.run.toTimeoutHigh P.Cswitch)) := le_max_left _ _
    dsimp [C]
    linarith
  have hOddTubeC :
      timeoutCompletedOddTrajectorySupportConstant
        P.run.toTimeoutHigh P.Cswitch ≤ C := by
    have h₁ : timeoutCompletedOddTrajectorySupportConstant
          P.run.toTimeoutHigh P.Cswitch ≤
        max
          (timeoutCompletedOddTrajectorySupportConstant
            P.run.toTimeoutHigh P.Cswitch)
          (timeoutCompletedRawTrajectorySupportConstant
            P.run.toTimeoutHigh P.Cswitch) := le_max_left _ _
    have h₂ := h₁.trans (le_max_right
      (max
        (max Cprof (fixedPolylogTargetConstant Amax))
        (max
          (2 * timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch)
          (timeoutCompletedRawClockSupportConstant
            P.run.toTimeoutHigh P.Cswitch))) _)
    dsimp [C]
    linarith
  have hRawTubeC :
      timeoutCompletedRawTrajectorySupportConstant
        P.run.toTimeoutHigh P.Cswitch ≤ C := by
    have h₁ : timeoutCompletedRawTrajectorySupportConstant
          P.run.toTimeoutHigh P.Cswitch ≤
        max
          (timeoutCompletedOddTrajectorySupportConstant
            P.run.toTimeoutHigh P.Cswitch)
          (timeoutCompletedRawTrajectorySupportConstant
            P.run.toTimeoutHigh P.Cswitch) := le_max_right _ _
    have h₂ := h₁.trans (le_max_right
      (max
        (max Cprof (fixedPolylogTargetConstant Amax))
        (max
          (2 * timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch)
          (timeoutCompletedRawClockSupportConstant
            P.run.toTimeoutHigh P.Cswitch))) _)
    dsimp [C]
    linarith
  have hC : 0 < C := hCprof.trans_le hCprofC
  have hShellFamily : ∀ᶠ M : ℕ in atTop,
      shellExceptionalRatio (timeoutStrengthenedEndpointGood P A R M) M ≤
        C * ((2 : ℝ) ^ (-(sharpMovingRankBuffer A M)) +
          (((M : ℝ) + 2) ^ (-P.epsilon))) + 4 / R M := by
    filter_upwards [hProfile] with M hProfile
    have herror0 : 0 ≤
        (2 : ℝ) ^ (-(sharpMovingRankBuffer A M)) +
          (((M : ℝ) + 2) ^ (-P.epsilon)) := by positivity
    exact hProfile.trans (add_le_add
      (mul_le_mul_of_nonneg_right hCprofC herror0) le_rfl)
  have hShell : ∀ᶠ M : ℕ in atTop,
      shellExceptionalRatio S M ≤
        C * ((2 : ℝ) ^ (-(sharpMovingRankBuffer A M)) +
          (((M : ℝ) + 2) ^ (-P.epsilon))) + 4 / R M := by
    filter_upwards [hShellFamily] with M hM
    rw [shellExceptionalRatio, shellBad_assembleDyadic]
    exact hM
  have hDense : NaturalDensityOne S := by
    simpa [S] using naturalDensityOne_of_sharpMovingShellErrorWithHeight
      (timeoutStrengthenedEndpointGood P A R) P.epsilon_pos hbuffer hR
        hShellFamily
  have hWitnessBase :=
    eventually_timeoutStrengthenedEndpointGood_has_shellWitness
      P hbuffer hUpper hR4
  have hc0 : 0 < c := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hinv : 0 < 1 / driftGap := one_div_pos.mpr driftGap_pos
    by_contra h
    have hcNonpos : c ≤ 0 := le_of_not_gt h
    have : c * Real.log 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hcNonpos hlog2.le
    linarith [P.clock_pressure]
  have hWitness : ∀ᶠ M : ℕ in atTop,
      ∀ n : ℕ, n ∈ dyadicShell M →
        n ∈ timeoutStrengthenedEndpointGood P A R M →
        ∃ k ell : ℕ,
          (k : ℝ) < c * Real.log n ∧
          |driftGap * (k : ℝ) - (M : ℝ)| ≤
            C * Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) ∧
          |(2 * driftGap / 3) * (ell : ℝ) - (M : ℝ)| ≤
            C * Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) ∧
          (∀ j : ℕ, j ≤ k →
            |shortcutLogDeviation n j| ≤
              C * Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2))) ∧
          (∀ j : ℕ, j ≤ k →
            |(oddCount n j : ℝ) - (j : ℝ) / 2| ≤
              C * Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2))) ∧
          (∀ i : ℕ, i ≤ ell →
            |rawLogDeviation n i| ≤
              C * Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2))) ∧
          ell = rawTime n k ∧
          rawOrbit ell n = orbit k n ∧
          (orbit k n : ℝ) < C * (Real.log n) ^ (A M) ∧
          (∀ j : ℕ, j ≤ k →
            (orbit j n : ℝ) ≤ (n : ℝ) * R M / 2) ∧
          (∀ i : ℕ, i ≤ ell →
            (rawOrbit i n : ℝ) ≤ (n : ℝ) * R M) := by
    filter_upwards [hWitnessBase] with M hWitnessBase
    intro n hnShell hnGood
    obtain ⟨k, ell, hk, hkCentered, hellCentered, hshortcutTube, hoddTube,
        hrawTube, hell, hlandingEq, hlanding, hshortcut, hraw⟩ :=
      hWitnessBase n hnShell hnGood
    have hroot0 : 0 ≤
        Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) :=
      Real.sqrt_nonneg _
    refine ⟨k, ell, hk.trans_le (shellClock_le_natLog hc0.le hnShell),
      hkCentered.trans (mul_le_mul_of_nonneg_right hClockC hroot0),
      hellCentered.trans (mul_le_mul_of_nonneg_right hRawClockC hroot0),
      (fun j hj ↦ (hshortcutTube j hj).trans
        (mul_le_mul_of_nonneg_right hClockC hroot0)),
      (fun j hj ↦ (hoddTube j hj).trans
        (mul_le_mul_of_nonneg_right hOddTubeC hroot0)),
      (fun i hi ↦ (hrawTube i hi).trans
        (mul_le_mul_of_nonneg_right hRawTubeC hroot0)),
      hell, hlandingEq, hlanding.trans_le ?_, hshortcut, hraw⟩
    have hlogPow0 : 0 ≤ (Real.log n) ^ (A M) := by positivity
    exact mul_le_mul_of_nonneg_right hTargetC hlogPow0
  have hAtLog := tendsto_natLogTwo_atTop.eventually hWitness
  refine ⟨S, C, hC, hDense, hShell, ?_⟩
  filter_upwards [hAtLog, eventually_ge_atTop (1 : ℕ)] with n hAtLog hn
  intro hnSet
  have hnpos : 0 < n := by omega
  let M := Nat.log 2 n
  have hnShell : n ∈ dyadicShell M := mem_dyadicShell_log hnpos
  have hnGood : n ∈ timeoutStrengthenedEndpointGood P A R M := by
    simpa [S, assembleDyadic, M] using hnSet
  simpa [M] using hAtLog n hnShell hnGood
end FirstPassageLinearTransport
