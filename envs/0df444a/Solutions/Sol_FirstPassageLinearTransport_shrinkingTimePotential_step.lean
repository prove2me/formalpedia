-- Prove2me | solution 1 for FirstPassageLinearTransport.shrinkingTimePotential_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:48:36.699738+00:00
-- url     : https://prove2.me/submissions/dc900049-57b9-4cd9-af04-2669e3bfed35

import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierRun
import Definitions.Def_FirstPassageLinearTransport_ShrinkingTimeSupport
import Theorems.Thm_FirstPassageLinearTransport_durationError_shrinkingHigh_le
import Theorems.Thm_FirstPassageLinearTransport_durationError_low_le
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_D_pos
import Theorems.Thm_FirstPassageLinearTransport_StageSetup_lowerTolerance_M0
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
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
    (P : ShrinkingBarrierRunData) {M S qPrev m q : ℕ}
    (hM : 1 ≤ M) (hm : 1 ≤ m) (hmPrev : qPrev = m + 1)
    (hq : if S ≤ m then
        (q : ℝ) ≤ (P.rHi : ℝ) * (m : ℝ)
      else (q : ℝ) ≤ (P.rLo : ℝ) * (m : ℝ)) :
    (if S ≤ m then durationError (shrinkingHighTolerance P M m) m
      else durationError P.etaLo m) + shrinkingTimePotential P M S q ≤
        shrinkingTimePotential P M S qPrev := by
  subst qPrev
  have hrHi0 : (0 : ℝ) ≤ P.rHi := P.pHi.r_pos.le
  have hrLo0 : (0 : ℝ) ≤ P.rLo := P.pLo.r_pos.le
  have hsHi1 := sqrt_rat_lt_one
    (by exact_mod_cast P.pHi.r_lt_one : P.rHi < 1)
  have hdHi : 0 < 1 - Real.sqrt (P.rHi : ℝ) := sub_pos.mpr hsHi1
  have hdLo : 0 < 1 - (P.rLo : ℝ) := sub_pos.mpr P.pLo.r_lt_one
  have hcoefHi : 0 < P.D + P.tau + 3 := by
    nlinarith [P.D_pos, P.pHi.eta_pos]
  have hcoefLo : 0 < 2 * P.etaLo + 3 := by nlinarith [P.pLo.eta_pos]
  have hlog0 : 0 ≤ Real.sqrt (Real.log ((M : ℝ) + 2)) := Real.sqrt_nonneg _
  by_cases hmHigh : S ≤ m
  · have hqBound : (q : ℝ) ≤ (P.rHi : ℝ) * (m : ℝ) := by
      simpa [hmHigh] using hq
    have hprevHigh : S < m + 1 := by omega
    have hcost := durationError_shrinkingHigh_le P hM hm
    by_cases hqHigh : S < q
    · have hsqrtq : Real.sqrt (q : ℝ) ≤
          Real.sqrt (P.rHi : ℝ) * Real.sqrt (m : ℝ) := by
        have hs := Real.sqrt_le_sqrt hqBound
        rw [Real.sqrt_mul hrHi0] at hs
        exact hs
      have hsqrtm : Real.sqrt (m : ℝ) ≤ Real.sqrt ((m + 1 : ℕ) : ℝ) :=
        Real.sqrt_le_sqrt (by norm_num)
      rw [if_pos hmHigh]
      simp only [shrinkingTimePotential, if_pos hqHigh, if_pos hprevHigh]
      have hscaled :
          (P.D + P.tau + 3) * Real.sqrt (Real.log ((M : ℝ) + 2)) *
              Real.sqrt (m : ℝ) +
              ((P.D + P.tau + 3) * Real.sqrt (Real.log ((M : ℝ) + 2)) *
                Real.sqrt (q : ℝ)) / (1 - Real.sqrt (P.rHi : ℝ)) ≤
            ((P.D + P.tau + 3) * Real.sqrt (Real.log ((M : ℝ) + 2)) *
              Real.sqrt ((m + 1 : ℕ) : ℝ)) /
                (1 - Real.sqrt (P.rHi : ℝ)) := by
        apply (le_div_iff₀ hdHi).2
        rw [add_mul, div_mul_cancel₀ _ hdHi.ne']
        have hmulq := mul_le_mul_of_nonneg_left hsqrtq
          (mul_nonneg hcoefHi.le hlog0)
        have hmulm := mul_le_mul_of_nonneg_left hsqrtm
          (mul_nonneg hcoefHi.le hlog0)
        nlinarith
      linarith
    · have hqLow : q ≤ S := by omega
      rw [if_pos hmHigh]
      simp only [shrinkingTimePotential, if_neg hqHigh, if_pos hprevHigh]
      have hlowReserve :
          ((2 * P.etaLo + 3) * (q : ℝ)) / (1 - (P.rLo : ℝ)) ≤
            ((2 * P.etaLo + 3) * (S : ℝ)) / (1 - (P.rLo : ℝ)) := by
        apply (div_le_div_iff_of_pos_right hdLo).2
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hqLow) hcoefLo.le
      have hsqrtm : Real.sqrt (m : ℝ) ≤ Real.sqrt ((m + 1 : ℕ) : ℝ) :=
        Real.sqrt_le_sqrt (by norm_num)
      have hhighPay :
          (P.D + P.tau + 3) * Real.sqrt (Real.log ((M : ℝ) + 2)) *
              Real.sqrt (m : ℝ) ≤
            ((P.D + P.tau + 3) * Real.sqrt (Real.log ((M : ℝ) + 2)) *
              Real.sqrt ((m + 1 : ℕ) : ℝ)) /
              (1 - Real.sqrt (P.rHi : ℝ)) := by
        have hbase := mul_le_mul_of_nonneg_left hsqrtm
          (mul_nonneg hcoefHi.le hlog0)
        have hdenLe : 1 - Real.sqrt (P.rHi : ℝ) ≤ 1 := by
          linarith [Real.sqrt_nonneg (P.rHi : ℝ)]
        have hdiv :
            (P.D + P.tau + 3) * Real.sqrt (Real.log ((M : ℝ) + 2)) *
                Real.sqrt ((m + 1 : ℕ) : ℝ) ≤
              ((P.D + P.tau + 3) * Real.sqrt (Real.log ((M : ℝ) + 2)) *
                Real.sqrt ((m + 1 : ℕ) : ℝ)) /
                (1 - Real.sqrt (P.rHi : ℝ)) := by
          apply (le_div_iff₀ hdHi).2
          nlinarith [mul_nonneg (mul_nonneg hcoefHi.le hlog0)
            (Real.sqrt_nonneg ((m + 1 : ℕ) : ℝ))]
        exact hbase.trans hdiv
      linarith
  · have hmLow : m < S := Nat.lt_of_not_ge hmHigh
    have hprevLow : ¬ S < m + 1 := by omega
    have hqBound : (q : ℝ) ≤ (P.rLo : ℝ) * (m : ℝ) := by
      simpa [hmHigh] using hq
    have hqLow : ¬ S < q := by
      have hm0R : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have hrmul : (P.rLo : ℝ) * (m : ℝ) ≤ (m : ℝ) := by
        nlinarith [P.pLo.r_lt_one]
      have hqm : q ≤ m := by exact_mod_cast hqBound.trans hrmul
      omega
    have hcost := durationError_low_le P hm
    rw [if_neg hmHigh]
    simp only [shrinkingTimePotential, if_neg hqLow, if_neg hprevLow]
    apply (le_div_iff₀ hdLo).2
    rw [add_mul, div_mul_cancel₀ _ hdLo.ne']
    have hcostMul := mul_le_mul_of_nonneg_right hcost hdLo.le
    have hqMul := mul_le_mul_of_nonneg_left hqBound hcoefLo.le
    push_cast
    nlinarith
end FirstPassageLinearTransport
