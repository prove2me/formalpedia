-- Prove2me | solution 1 for FirstPassageLinearTransport.eventually_timeoutRun_elapsed_centered
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:15:49.069803+00:00
-- url     : https://prove2.me/submissions/644135f4-dd1a-4789-a052-8cca4892a78e

import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointAsymptotics
import Definitions.Def_FirstPassageLinearTransport_AsymptoticBounds
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_TimeoutOrbitCeiling
import Theorems.Thm_FirstPassageLinearTransport_ShrinkingRecertificationRun_deviation_add_potential_le
import Theorems.Thm_FirstPassageLinearTransport_StageSetup_lowerTolerance_M0
import Theorems.Thm_FirstPassageLinearTransport_TimeoutRecertificationRun_deviation_add_potential_le
import Theorems.Thm_FirstPassageLinearTransport_a0_lt_one
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_driftGap_lt_a0
import Theorems.Thm_FirstPassageLinearTransport_driftGap_pos
import Theorems.Thm_FirstPassageLinearTransport_eventually_shrinkingSwitchRank_lt_source
import Theorems.Thm_FirstPassageLinearTransport_eventually_timeoutTimePotential_source_le_sqrt
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
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_shrinkingHighSetup_M0
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_stoppedBallotValue_cons
import Theorems.Thm_FirstPassageLinearTransport_timeoutTimePotential_nonneg
import Theorems.Thm_FirstPassageLinearTransport_timeout_switch_sq_le_source_potential
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
attribute [local simp] FirstPassageLinearTransport.rawOrbit_zero
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
    (P : TimeoutHighRunData) {K₀ C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ M : ℕ in atTop, ∀ {L n elapsed q : ℕ},
      q ≤ shrinkingSwitchRank C M →
      TimeoutRecertificationRun P K₀ L M
        (shrinkingSwitchRank C M) n elapsed q →
      |driftGap * (elapsed : ℝ) - (M : ℝ)| ≤
        timeoutTimeSupportConstant P C *
          Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) := by
  have hPotential := eventually_timeoutTimePotential_source_le_sqrt P hC
  have hSwitch := eventually_shrinkingSwitchRank_lt_source hC
  filter_upwards [hPotential, hSwitch, eventually_ge_atTop (1 : ℕ)]
    with M hPotential hSwitch hM
  intro L n elapsed q hqS hrun
  let S := shrinkingSwitchRank C M
  let sourcePotential := timeoutTimePotential P M S (M + 1)
  let root := Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2))
  have hdev := hrun.deviation_add_potential_le hM
  have hpotq0 := timeoutTimePotential_nonneg P M S q
  have hlocal :
      |driftGap * (elapsed : ℝ) -
          (((M + 1 : ℕ) : ℝ) - (q : ℝ))| ≤ sourcePotential := by
    dsimp [sourcePotential, S]
    linarith
  have hshift :
      |(((M + 1 : ℕ) : ℝ) - (q : ℝ)) - (M : ℝ)| ≤ (q : ℝ) + 1 := by
    have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
    push_cast
    rw [abs_le]
    constructor <;> linarith
  have hSsq : (S : ℝ) ≤ (S : ℝ) ^ 2 := by
    by_cases hS0 : S = 0
    · simp [hS0]
    · have hS1 : (1 : ℝ) ≤ (S : ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hS0)
      nlinarith [sq_nonneg ((S : ℝ) - 1)]
  have hqR : (q : ℝ) ≤ (S : ℝ) := by
    exact_mod_cast hqS
  have hreserve : (S : ℝ) ^ 2 ≤ sourcePotential := by
    dsimp [sourcePotential, S]
    exact timeout_switch_sq_le_source_potential P (by omega)
  have hcenter :
      |driftGap * (elapsed : ℝ) - (M : ℝ)| ≤
        2 * sourcePotential + 1 := by
    calc
      |driftGap * (elapsed : ℝ) - (M : ℝ)| =
          |(driftGap * (elapsed : ℝ) -
              (((M + 1 : ℕ) : ℝ) - (q : ℝ))) +
            ((((M + 1 : ℕ) : ℝ) - (q : ℝ)) - (M : ℝ))| := by ring
      _ ≤ |driftGap * (elapsed : ℝ) -
              (((M + 1 : ℕ) : ℝ) - (q : ℝ))| +
            |(((M + 1 : ℕ) : ℝ) - (q : ℝ)) - (M : ℝ)| := abs_add_le _ _
      _ ≤ sourcePotential + ((q : ℝ) + 1) := add_le_add hlocal hshift
      _ ≤ 2 * sourcePotential + 1 := by nlinarith
  have hpot0 : 0 ≤ sourcePotential := by
    dsimp [sourcePotential, S]
    exact timeoutTimePotential_nonneg P M (shrinkingSwitchRank C M) (M + 1)
  have hgap_le_one : driftGap ≤ 1 := by
    linarith [driftGap_lt_a0, a0_lt_one]
  have hscaled : 2 * sourcePotential ≤ 2 * sourcePotential / driftGap := by
    rw [le_div_iff₀ driftGap_pos]
    nlinarith
  calc
    |driftGap * (elapsed : ℝ) - (M : ℝ)| ≤
        2 * sourcePotential + 1 := hcenter
    _ ≤ 1 + 2 * sourcePotential / driftGap := by linarith
    _ ≤ timeoutTimeSupportConstant P C * root := by
      simpa [sourcePotential, S, root, div_eq_mul_inv, mul_assoc] using hPotential
end FirstPassageLinearTransport
