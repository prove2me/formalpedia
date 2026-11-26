-- Prove2me | solution 1 for FirstPassageLinearTransport.shrinkingFeasibleTimes_card_le_potential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:52:07.912932+00:00
-- url     : https://prove2.me/submissions/5b009374-a8ce-4a4a-8630-a00d0a8749e6

import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierRun
import Definitions.Def_FirstPassageLinearTransport_ShrinkingTimeSupport
import Theorems.Thm_FirstPassageLinearTransport_ShrinkingRecertificationRun_deviation_add_potential_le
import Theorems.Thm_FirstPassageLinearTransport_mem_shrinkingFeasibleTimes
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_D_pos
import Theorems.Thm_FirstPassageLinearTransport_StageSetup_lowerTolerance_M0
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
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
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_shrinkingHighSetup_M0
attribute [local simp] FirstPassageLinearTransport.StageSetup.lowerTolerance_M0
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_firstBadLandingEnvelope
attribute [local simp] FirstPassageLinearTransport.mem_generatedFirstBadSources
attribute [local simp] FirstPassageLinearTransport.mem_landingBad
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTaggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTransportedSources
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTransportedSourcesAtTimes
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.rawOrbit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero
attribute [local simp] FirstPassageLinearTransport.shrinkingHighSetup_M0


attribute [local simp] FirstPassageLinearTransport.mem_shrinkingFeasibleTimes
section
namespace FirstPassageLinearTransport
open scoped Real
noncomputable section
private theorem sqrt_rat_lt_one
    {r : ℚ} (hr1 : r < 1) :
    Real.sqrt (r : ℝ) < 1 := by
  rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)]
  norm_num
  exact_mod_cast hr1
end
end FirstPassageLinearTransport
end

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (P : ShrinkingBarrierRunData) {M S q : ℕ} (hM : 1 ≤ M) :
    (shrinkingFeasibleTimes P M S q).card ≤
      ⌈(1 + 2 * shrinkingTimePotential P M S (M + 1) / driftGap)⌉₊ := by
  classical
  let times := shrinkingFeasibleTimes P M S q
  by_cases hne : times.Nonempty
  · have hspan := finset_card_le_one_add_span times hne
    have hmaxMem := times.max'_mem hne
    have hminMem := times.min'_mem hne
    rcases mem_shrinkingFeasibleTimes.mp hmaxMem with ⟨_hmaxH, xmax, hxShell, hxrun⟩
    rcases mem_shrinkingFeasibleTimes.mp hminMem with ⟨_hminH, xmin, hxminShell, hxminrun⟩
    have hxdev := (hxrun.deviation_add_potential_le hM)
    have hmindev := (hxminrun.deviation_add_potential_le hM)
    have hpot0 : 0 ≤ shrinkingTimePotential P M S q := by
      have hdHi : 0 < 1 - Real.sqrt (P.rHi : ℝ) := sub_pos.mpr
        (sqrt_rat_lt_one
          (by exact_mod_cast P.pHi.r_lt_one : P.rHi < 1))
      have hdLo : 0 < 1 - (P.rLo : ℝ) := sub_pos.mpr P.pLo.r_lt_one
      have hcoefHi : 0 ≤ P.D + P.tau + 3 := by
        nlinarith [P.D_pos, P.pHi.eta_pos]
      have hcoefLo : 0 ≤ 2 * P.etaLo + 3 := by
        nlinarith [P.pLo.eta_pos]
      unfold shrinkingTimePotential
      split_ifs <;> positivity
    have hxabs :
        |driftGap * (times.max' hne : ℝ) -
          (((M + 1 : ℕ) : ℝ) - (q : ℝ))| ≤
            shrinkingTimePotential P M S (M + 1) := by
      linarith
    have hminabs :
        |driftGap * (times.min' hne : ℝ) -
          (((M + 1 : ℕ) : ℝ) - (q : ℝ))| ≤
            shrinkingTimePotential P M S (M + 1) := by
      linarith
    have hdiff :
        ((times.max' hne : ℕ) : ℝ) - (times.min' hne : ℝ) ≤
          2 * shrinkingTimePotential P M S (M + 1) / driftGap := by
      rw [le_div_iff₀ driftGap_pos]
      have hmaxUpper := (abs_le.mp hxabs).2
      have hminLower := (abs_le.mp hminabs).1
      nlinarith
    have hcardR : ((times.card : ℕ) : ℝ) ≤
        1 + 2 * shrinkingTimePotential P M S (M + 1) / driftGap := by
      have hspanR : ((times.card : ℕ) : ℝ) ≤
          1 + (times.max' hne : ℝ) - (times.min' hne : ℝ) := by
        exact_mod_cast hspan
      linarith
    have hceil := Nat.le_ceil
      (1 + 2 * shrinkingTimePotential P M S (M + 1) / driftGap)
    exact_mod_cast hcardR.trans hceil
  · have hempty : times = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hactual : shrinkingFeasibleTimes P M S q = ∅ := by
      simpa [times] using hempty
    rw [hactual]
    exact Nat.zero_le _
end FirstPassageLinearTransport
