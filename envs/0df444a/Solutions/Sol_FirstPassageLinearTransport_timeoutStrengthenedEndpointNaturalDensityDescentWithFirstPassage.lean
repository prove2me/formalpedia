-- Prove2me | solution 1 for FirstPassageLinearTransport.timeoutStrengthenedEndpointNaturalDensityDescentWithFirstPassage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:41:50.295444+00:00
-- url     : https://prove2.me/submissions/b152d88b-c386-45b6-af35-42082e714da4

import Definitions.Def_FirstPassageLinearTransport_MovingEndpointAssembly
import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointAsymptotics
import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointWitness
import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointNaturalDensity
import Theorems.Thm_FirstPassageLinearTransport_timeoutStrengthenedEndpointNaturalDensityDescent
import Theorems.Thm_FirstPassageLinearTransport_StageSetup_lowerTolerance_M0
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_fixedPolylogClockCritical_pos
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
import Theorems.Thm_FirstPassageLinearTransport_one_le_timeoutProfileRoot
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawFirstPassageTime_self
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcutFirstPassageTime_self
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_shrinkingHighSetup_M0
import Theorems.Thm_FirstPassageLinearTransport_simultaneousFirstPassageTime_centered_profile
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
    (hAmax : 0 < Amax)
    (hc : fixedPolylogClockCritical < c)
    (hbeta : 0 < beta)
    (hbuffer : Tendsto (sharpMovingRankBuffer A) atTop atTop)
    (hUpper : ∀ᶠ M : ℕ in atTop, A M ≤ Amax)
    (hR : Tendsto R atTop atTop) :
    ∃ S : Set ℕ, ∃ K eps : ℝ,
      0 < K ∧ 0 < eps ∧ NaturalDensityOne S ∧
      (∀ᶠ M : ℕ in atTop,
        shellExceptionalRatio S M ≤
          K * ((2 : ℝ) ^ (-(sharpMovingRankBuffer A M)) +
            (((M : ℝ) + 2) ^ (-eps))) + 4 / R M) ∧
      (∀ᶠ n : ℕ in atTop, n ∈ S →
        ∃ k ell : ℕ,
          (k : ℝ) < c * Real.log n ∧
          |driftGap * (k : ℝ) - (Nat.log 2 n : ℝ)| ≤
            K * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
              Real.log ((Nat.log 2 n : ℝ) + 2)) ∧
          |(2 * driftGap / 3) * (ell : ℝ) - (Nat.log 2 n : ℝ)| ≤
            K * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
              Real.log ((Nat.log 2 n : ℝ) + 2)) ∧
          (∀ j : ℕ, j ≤ k →
            |shortcutLogDeviation n j| ≤
              K * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
                Real.log ((Nat.log 2 n : ℝ) + 2))) ∧
          (∀ j : ℕ, j ≤ k →
            |(oddCount n j : ℝ) - (j : ℝ) / 2| ≤
              K * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
                Real.log ((Nat.log 2 n : ℝ) + 2))) ∧
          (∀ i : ℕ, i ≤ ell →
            |rawLogDeviation n i| ≤
              K * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
                Real.log ((Nat.log 2 n : ℝ) + 2))) ∧
          ell = rawTime n k ∧
          rawOrbit ell n = orbit k n ∧
          (orbit k n : ℝ) <
            K * (Real.log n) ^ (A (Nat.log 2 n)) ∧
          (∀ j : ℕ, j ≤ k →
            (orbit j n : ℝ) ≤
              (n : ℝ) * R (Nat.log 2 n) / 2) ∧
          (∀ i : ℕ, i ≤ ell →
            (rawOrbit i n : ℝ) ≤
              (n : ℝ) * R (Nat.log 2 n)) ∧
          (∀ z : ℝ, (orbit k n : ℝ) ≤ z → z ≤ (n : ℝ) →
            |(shortcutFirstPassageTime n z : ℝ) -
                fixedPolylogClockCritical * Real.log ((n : ℝ) / z)| +
              |(rawFirstPassageTime n z : ℝ) -
                (3 / 2) * fixedPolylogClockCritical *
                  Real.log ((n : ℝ) / z)| ≤
                K * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
                  Real.log ((Nat.log 2 n : ℝ) + 2)) ∧
            rawOrbit (rawFirstPassageTime n z) n =
              orbit (shortcutFirstPassageTime n z) n)) := by
  obtain ⟨S, C₀, eps, hC₀, heps, hDense, hShell, hWitness⟩ :=
    timeoutStrengthenedEndpointNaturalDensityDescent
      hAmax hc hbeta hbuffer hUpper hR
  let Kprofile := (5 / 2) * fixedPolylogClockCritical *
    (C₀ + Real.log 2)
  let K := max C₀ Kprofile + 1
  have hC₀K : C₀ ≤ K := by
    dsimp [K]
    linarith [le_max_left C₀ Kprofile]
  have hProfileK : Kprofile ≤ K := by
    dsimp [K]
    linarith [le_max_right C₀ Kprofile]
  have hK : 0 < K := hC₀.trans_le hC₀K
  have hShell' : ∀ᶠ M : ℕ in atTop,
      shellExceptionalRatio S M ≤
        K * ((2 : ℝ) ^ (-(sharpMovingRankBuffer A M)) +
          (((M : ℝ) + 2) ^ (-eps))) + 4 / R M := by
    filter_upwards [hShell] with M hShell
    have herror0 : 0 ≤
        (2 : ℝ) ^ (-(sharpMovingRankBuffer A M)) +
          (((M : ℝ) + 2) ^ (-eps)) := by positivity
    exact hShell.trans (add_le_add
      (mul_le_mul_of_nonneg_right hC₀K herror0) le_rfl)
  have hLogRank : ∀ᶠ n : ℕ in atTop, 1 ≤ Nat.log 2 n :=
    tendsto_natLogTwo_atTop.eventually (eventually_ge_atTop 1)
  have hWitness' : ∀ᶠ n : ℕ in atTop, n ∈ S →
      ∃ k ell : ℕ,
        (k : ℝ) < c * Real.log n ∧
        |driftGap * (k : ℝ) - (Nat.log 2 n : ℝ)| ≤
          K * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
            Real.log ((Nat.log 2 n : ℝ) + 2)) ∧
        |(2 * driftGap / 3) * (ell : ℝ) - (Nat.log 2 n : ℝ)| ≤
          K * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
            Real.log ((Nat.log 2 n : ℝ) + 2)) ∧
        (∀ j : ℕ, j ≤ k →
          |shortcutLogDeviation n j| ≤
            K * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
              Real.log ((Nat.log 2 n : ℝ) + 2))) ∧
        (∀ j : ℕ, j ≤ k →
          |(oddCount n j : ℝ) - (j : ℝ) / 2| ≤
            K * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
              Real.log ((Nat.log 2 n : ℝ) + 2))) ∧
        (∀ i : ℕ, i ≤ ell →
          |rawLogDeviation n i| ≤
            K * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
              Real.log ((Nat.log 2 n : ℝ) + 2))) ∧
        ell = rawTime n k ∧
        rawOrbit ell n = orbit k n ∧
        (orbit k n : ℝ) < K * (Real.log n) ^ (A (Nat.log 2 n)) ∧
        (∀ j : ℕ, j ≤ k →
          (orbit j n : ℝ) ≤ (n : ℝ) * R (Nat.log 2 n) / 2) ∧
        (∀ i : ℕ, i ≤ ell →
          (rawOrbit i n : ℝ) ≤ (n : ℝ) * R (Nat.log 2 n)) ∧
        (∀ z : ℝ, (orbit k n : ℝ) ≤ z → z ≤ (n : ℝ) →
          |(shortcutFirstPassageTime n z : ℝ) -
              fixedPolylogClockCritical * Real.log ((n : ℝ) / z)| +
            |(rawFirstPassageTime n z : ℝ) -
              (3 / 2) * fixedPolylogClockCritical *
                Real.log ((n : ℝ) / z)| ≤
              K * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
                Real.log ((Nat.log 2 n : ℝ) + 2)) ∧
          rawOrbit (rawFirstPassageTime n z) n =
            orbit (shortcutFirstPassageTime n z) n) := by
    filter_upwards [hWitness, hLogRank, eventually_ge_atTop (1 : ℕ)]
      with n hWitness hM hn
    intro hnS
    obtain ⟨k, ell, hk, hkCentered, hellCentered, hshortcutTube, hoddTube,
        hrawTube, hell, hlandingEq, hlanding, hshortcut, hraw⟩ := hWitness hnS
    let root := Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
      Real.log ((Nat.log 2 n : ℝ) + 2))
    have hroot0 : 0 ≤ root := Real.sqrt_nonneg _
    have hroot1 : 1 ≤ root := by
      simpa [root] using one_le_timeoutProfileRoot hM
    have hnpos : 0 < n := by omega
    have hpow0 : 0 ≤ (Real.log n) ^ (A (Nat.log 2 n)) := by positivity
    have hactual : ∀ z : ℝ, (orbit k n : ℝ) ≤ z → z ≤ (n : ℝ) →
        |(shortcutFirstPassageTime n z : ℝ) -
            fixedPolylogClockCritical * Real.log ((n : ℝ) / z)| +
          |(rawFirstPassageTime n z : ℝ) -
            (3 / 2) * fixedPolylogClockCritical *
              Real.log ((n : ℝ) / z)| ≤ K * root ∧
        rawOrbit (rawFirstPassageTime n z) n =
          orbit (shortcutFirstPassageTime n z) n := by
      intro z hzLanding hzSource
      have hsim := simultaneousFirstPassageTime_centered_profile
        hnpos hzLanding hzSource hell
        (fun j hj ↦ by simpa [root] using hshortcutTube j hj)
        (fun i hi ↦ by simpa [root] using hrawTube i hi)
      have hlogTwo0 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
      have hinner : C₀ * root + Real.log 2 ≤
          (C₀ + Real.log 2) * root := by
        nlinarith [mul_nonneg hlogTwo0 (sub_nonneg.mpr hroot1)]
      have hcoef0 : 0 ≤ (5 / 2) * fixedPolylogClockCritical := by
        exact mul_nonneg (by norm_num) fixedPolylogClockCritical_pos.le
      have hprofile :
          fixedPolylogClockCritical * (C₀ * root + Real.log 2) +
              (3 / 2) * fixedPolylogClockCritical *
                (C₀ * root + Real.log 2) ≤ K * root := by
        calc
          _ = (5 / 2) * fixedPolylogClockCritical *
                (C₀ * root + Real.log 2) := by ring
          _ ≤ (5 / 2) * fixedPolylogClockCritical *
                ((C₀ + Real.log 2) * root) :=
            mul_le_mul_of_nonneg_left hinner hcoef0
          _ = Kprofile * root := by simp [Kprofile]; ring
          _ ≤ K * root := mul_le_mul_of_nonneg_right hProfileK hroot0
      exact ⟨hsim.1.trans hprofile, hsim.2⟩
    refine ⟨k, ell, hk,
      hkCentered.trans (mul_le_mul_of_nonneg_right hC₀K hroot0),
      hellCentered.trans (mul_le_mul_of_nonneg_right hC₀K hroot0),
      (fun j hj ↦ (hshortcutTube j hj).trans
        (mul_le_mul_of_nonneg_right hC₀K hroot0)),
      (fun j hj ↦ (hoddTube j hj).trans
        (mul_le_mul_of_nonneg_right hC₀K hroot0)),
      (fun i hi ↦ (hrawTube i hi).trans
        (mul_le_mul_of_nonneg_right hC₀K hroot0)),
      hell, hlandingEq,
      hlanding.trans_le (mul_le_mul_of_nonneg_right hC₀K hpow0),
      hshortcut, hraw, hactual⟩
  exact ⟨S, K, eps, hK, heps, hDense, hShell', hWitness'⟩
end FirstPassageLinearTransport
