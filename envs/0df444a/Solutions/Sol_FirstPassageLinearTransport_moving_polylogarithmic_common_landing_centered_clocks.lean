-- Prove2me | solution 1 for FirstPassageLinearTransport.moving_polylogarithmic_common_landing_centered_clocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:40:23.578848+00:00
-- url     : https://prove2.me/submissions/e05cf21d-7244-42b4-bb69-192e629f4471

import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointNaturalDensity
import Definitions.Def_FirstPassageLinearTransport_PolylogExceptionalCount
import Definitions.Def_FirstPassageLinearTransport_CriticalEndpointConsequences
import Theorems.Thm_FirstPassageLinearTransport_tendsto_shellRankRpow_atTop
import Theorems.Thm_FirstPassageLinearTransport_StageSetup_lowerTolerance_M0
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_exists_movingEndpointParameterPackage_epsilon_gt
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
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
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawFirstPassageTime_self
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcutFirstPassageTime_self
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_shrinkingHighSetup_M0
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_stoppedBallotValue_cons
import Theorems.Thm_FirstPassageLinearTransport_timeoutStrengthenedEndpointNaturalDensityDescentOfPackage
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
    {A : ℕ → ℝ} {Amax c beta N : ℝ}
    (hAmax : 0 < Amax)
    (hc : fixedPolylogClockCritical < c)
    (hbeta : 0 < beta)
    (hN : 0 < N)
    (hbuffer : Tendsto (sharpMovingRankBuffer A) atTop atTop)
    (hUpper : ∀ᶠ M : ℕ in atTop, A M ≤ Amax) :
    ∃ S : Set ℕ, ∃ C : ℝ,
      0 < C ∧ NaturalDensityOne S ∧
      (∀ᶠ M : ℕ in atTop,
        shellExceptionalRatio S M ≤
          C * ((2 : ℝ) ^ (-(sharpMovingRankBuffer A M)) +
            (((M : ℝ) + 2) ^ (-N)))) ∧
      (∀ᶠ n : ℕ in atTop, n ∈ S →
        ∃ k ell : ℕ,
          (k : ℝ) < c * Real.log n ∧
          |driftGap * (k : ℝ) - (Nat.log 2 n : ℝ)| ≤
            C * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
              Real.log ((Nat.log 2 n : ℝ) + 2)) ∧
          |(2 * driftGap / 3) * (ell : ℝ) - (Nat.log 2 n : ℝ)| ≤
            C * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
              Real.log ((Nat.log 2 n : ℝ) + 2)) ∧
          ell = rawTime n k ∧
          rawOrbit ell n = orbit k n ∧
          (orbit k n : ℝ) <
            C * (Real.log n) ^ (A (Nat.log 2 n)) ∧
          (∀ j : ℕ, j ≤ k →
            (orbit j n : ℝ) ≤
              (n : ℝ) * (((Nat.log 2 n : ℝ) + 2) ^ N)) ∧
          (∀ i : ℕ, i ≤ ell →
            (rawOrbit i n : ℝ) ≤
              (n : ℝ) * (((Nat.log 2 n : ℝ) + 2) ^ N))) := by
  obtain ⟨P, hPeps⟩ :=
    exists_movingEndpointParameterPackage_epsilon_gt
      hAmax hc hbeta hN
  let R : ℕ → ℝ := fun M => ((M : ℝ) + 2) ^ N
  have hRT : Tendsto R atTop atTop := by
    simpa [R] using tendsto_shellRankRpow_atTop hN
  obtain ⟨S, C₀, hC₀, hDense, hShell, hWitness⟩ :=
    timeoutStrengthenedEndpointNaturalDensityDescentOfPackage
      P hbuffer hUpper hRT
  let C := C₀ + 4
  have hC : 0 < C := by dsimp [C]; linarith
  have hShell' : ∀ᶠ M : ℕ in atTop,
      shellExceptionalRatio S M ≤
        C * ((2 : ℝ) ^ (-(sharpMovingRankBuffer A M)) +
          (((M : ℝ) + 2) ^ (-N))) := by
    filter_upwards [hShell] with M hShell
    let x : ℝ := (M : ℝ) + 2
    have hx1 : 1 ≤ x := by
      have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
      dsimp [x]
      linarith
    have hx0 : 0 ≤ x := zero_le_one.trans hx1
    have hpow : x ^ (-P.epsilon) ≤ x ^ (-N) := by
      exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have hheight : 4 / R M = 4 * x ^ (-N) := by
      dsimp [R, x]
      rw [Real.rpow_neg (by positivity)]
      rfl
    have ha0 : 0 ≤ (2 : ℝ) ^ (-(sharpMovingRankBuffer A M)) := by positivity
    have hb0 : 0 ≤ x ^ (-N) := Real.rpow_nonneg hx0 _
    have hbE0 : 0 ≤ x ^ (-P.epsilon) := Real.rpow_nonneg hx0 _
    rw [hheight] at hShell
    dsimp [C]
    dsimp [R, x] at hShell ⊢
    nlinarith [hC₀.le]
  have hWitness' : ∀ᶠ n : ℕ in atTop, n ∈ S →
      ∃ k ell : ℕ,
        (k : ℝ) < c * Real.log n ∧
        |driftGap * (k : ℝ) - (Nat.log 2 n : ℝ)| ≤
          C * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
            Real.log ((Nat.log 2 n : ℝ) + 2)) ∧
        |(2 * driftGap / 3) * (ell : ℝ) - (Nat.log 2 n : ℝ)| ≤
          C * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
            Real.log ((Nat.log 2 n : ℝ) + 2)) ∧
        ell = rawTime n k ∧
        rawOrbit ell n = orbit k n ∧
        (orbit k n : ℝ) <
          C * (Real.log n) ^ (A (Nat.log 2 n)) ∧
        (∀ j : ℕ, j ≤ k →
          (orbit j n : ℝ) ≤
            (n : ℝ) * (((Nat.log 2 n : ℝ) + 2) ^ N)) ∧
        (∀ i : ℕ, i ≤ ell →
          (rawOrbit i n : ℝ) ≤
            (n : ℝ) * (((Nat.log 2 n : ℝ) + 2) ^ N)) := by
    filter_upwards [hWitness] with n hWitness hnS
    obtain ⟨k, ell, hk, hkCentered, hellCentered, _hshortcutTube,
        _hoddTube, _hrawTube, hell, hlandingEq, hlanding, hshortcut, hraw⟩ :=
      hWitness hnS
    let root := Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
      Real.log ((Nat.log 2 n : ℝ) + 2))
    have hroot0 : 0 ≤ root := Real.sqrt_nonneg _
    have hpow0 : 0 ≤ (Real.log n) ^ (A (Nat.log 2 n)) := by positivity
    have hR0 : 0 ≤ R (Nat.log 2 n) := by dsimp [R]; positivity
    refine ⟨k, ell, hk,
      hkCentered.trans ?_, hellCentered.trans ?_, hell, hlandingEq,
      hlanding.trans_le ?_, ?_, ?_⟩
    · dsimp [C, root]
      nlinarith
    · dsimp [C, root]
      nlinarith
    · dsimp [C]
      nlinarith
    · intro j hj
      have hjBound := hshortcut j hj
      dsimp [R] at hjBound ⊢
      nlinarith
    · intro i hi
      simpa [R] using hraw i hi
  exact ⟨S, C, hC, hDense, hShell', hWitness'⟩
end FirstPassageLinearTransport
