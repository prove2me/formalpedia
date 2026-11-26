-- Prove2me | solution 1 for FirstPassageLinearTransport.timeoutFeasibleTimes_card_le_potential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:15:51.074094+00:00
-- url     : https://prove2.me/submissions/135764ea-d1ed-48f2-8c56-fb0bfaec36ff

import Definitions.Def_FirstPassageLinearTransport_TimeoutRun
import Definitions.Def_FirstPassageLinearTransport_ShrinkingSchedules
import Definitions.Def_FirstPassageLinearTransport_TimeoutTimeSupport
import Theorems.Thm_FirstPassageLinearTransport_timeoutTimePotential_nonneg
import Theorems.Thm_FirstPassageLinearTransport_TimeoutRecertificationRun_deviation_add_potential_le
import Theorems.Thm_FirstPassageLinearTransport_ShrinkingRecertificationRun_deviation_add_potential_le
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
import Theorems.Thm_FirstPassageLinearTransport_finset_card_le_one_add_span
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_firstBadLandingEnvelope
import Theorems.Thm_FirstPassageLinearTransport_mem_generatedFirstBadSources
import Theorems.Thm_FirstPassageLinearTransport_mem_landingBad
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTaggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTransportedSources
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTransportedSourcesAtTimes
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_shrinkingFeasibleTimes
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
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
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
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
    (P : TimeoutHighRunData) (K₀ : ℝ)
    {L M S q : ℕ} (hM : 1 ≤ M) :
    (timeoutFeasibleTimes P K₀ L M S q).card ≤
      ⌈(1 + 2 * timeoutTimePotential P M S (M + 1) / driftGap)⌉₊ := by
  classical
  let times := timeoutFeasibleTimes P K₀ L M S q
  by_cases hne : times.Nonempty
  · have hspan := finset_card_le_one_add_span times hne
    have hmaxMem := times.max'_mem hne
    have hminMem := times.min'_mem hne
    have hmaxMem' : times.max' hne ∈ timeoutFeasibleTimes P K₀ L M S q := by
      simpa [times] using hmaxMem
    have hminMem' : times.min' hne ∈ timeoutFeasibleTimes P K₀ L M S q := by
      simpa [times] using hminMem
    rw [timeoutFeasibleTimes, Finset.mem_filter] at hmaxMem' hminMem'
    rcases hmaxMem'.2 with ⟨xmax, hxShell, hxrun⟩
    rcases hminMem'.2 with ⟨xmin, hxminShell, hxminrun⟩
    have hxdev := hxrun.deviation_add_potential_le hM
    have hmindev := hxminrun.deviation_add_potential_le hM
    have hpotq0 := timeoutTimePotential_nonneg P M S q
    have hxabs :
        |driftGap * (times.max' hne : ℝ) -
          (((M + 1 : ℕ) : ℝ) - (q : ℝ))| ≤
            timeoutTimePotential P M S (M + 1) := by
      linarith
    have hminabs :
        |driftGap * (times.min' hne : ℝ) -
          (((M + 1 : ℕ) : ℝ) - (q : ℝ))| ≤
            timeoutTimePotential P M S (M + 1) := by
      linarith
    have hdiff :
        ((times.max' hne : ℕ) : ℝ) - (times.min' hne : ℝ) ≤
          2 * timeoutTimePotential P M S (M + 1) / driftGap := by
      rw [le_div_iff₀ driftGap_pos]
      have hmaxUpper := (abs_le.mp hxabs).2
      have hminLower := (abs_le.mp hminabs).1
      nlinarith
    have hcardR : ((times.card : ℕ) : ℝ) ≤
        1 + 2 * timeoutTimePotential P M S (M + 1) / driftGap := by
      have hspanR : ((times.card : ℕ) : ℝ) ≤
          1 + (times.max' hne : ℝ) - (times.min' hne : ℝ) := by
        exact_mod_cast hspan
      linarith
    have hceil := Nat.le_ceil
      (1 + 2 * timeoutTimePotential P M S (M + 1) / driftGap)
    exact_mod_cast hcardR.trans hceil
  · have hempty : times = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hactual : timeoutFeasibleTimes P K₀ L M S q = ∅ := by
      simpa [times] using hempty
    rw [hactual]
    exact Nat.zero_le _
end FirstPassageLinearTransport
