-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_01_two_record_discount_pathwise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:37:17.332689+00:00
-- url     : https://prove2.me/submissions/08f72a40-8ef6-4900-90f2-7c8c73c36461

import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_reflected_next_record_future_ruin_iff
import Theorems.Thm_AvramDividend_Classical_levyPath_bddAbove_Icc
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_attains_peak
import Theorems.Thm_AvramDividend_Classical_nextRecord_upclock_eq_add_shifted_inf
import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_mono_threshold

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The original reflected-killed discounted next-record payoff factors
    pathwise at the preceding strict upward record, including infinite clocks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b c q : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (ω : Ω) :
    (if twoSidedExitUpTime X (b + c) ω < barrierRuinTime X a ω then
       ENNReal.ofReal (Real.exp
         (-(q * (twoSidedExitUpTime X (b + c) ω).toReal))) else 0) =
    (let u : ℝ≥0 := (twoSidedExitUpTime X b ω).toNNReal
     let U : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 //
       c < X.X (u + t) ω - X.X u ω}, (i.1 : ℝ≥0∞)
     let D : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 //
       X.X (u + t) ω -
         sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Icc 0 t) < -a},
       (i.1 : ℝ≥0∞)
     if twoSidedExitUpTime X b ω < barrierRuinTime X a ω then
       ENNReal.ofReal (Real.exp (-(q * (u : ℝ)))) *
         (if U < D then ENNReal.ofReal (Real.exp (-(q * U.toReal))) else 0)
     else 0) := by
  classical
  by_cases hB : twoSidedExitUpTime X b ω < barrierRuinTime X a ω
  · let u : ℝ≥0 := (twoSidedExitUpTime X b ω).toNNReal
    have hFinite : twoSidedExitUpTime X b ω ≠ ⊤ :=
      ne_top_of_lt (lt_of_lt_of_le hB le_top)
    have hu : (u : ℝ≥0∞) = twoSidedExitUpTime X b ω :=
      ENNReal.coe_toNNReal hFinite
    have hBefore : (u : ℝ≥0∞) < barrierRuinTime X a ω := by
      rw [hu]
      exact hB
    have hBdd := levyPath_bddAbove_Icc X ω u
    have hE := avram_wave3_01_reflected_next_record_future_ruin_iff
      X a b c ha hb.le hc.le ω u hu hBefore hBdd
    have hAt : X.X u ω = b :=
      (firstUpcrossing_attains_peak X b hb.le ω u
        (by simpa only [twoSidedExitUpTime] using hu)).1
    have hNext := nextRecord_upclock_eq_add_shifted_inf
      X b c hc.le u ω hu hAt
    let U : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 //
      c < X.X (u + t) ω - X.X u ω}, (i.1 : ℝ≥0∞)
    let D : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 //
      X.X (u + t) ω -
        sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Icc 0 t) < -a},
      (i.1 : ℝ≥0∞)
    by_cases hN :
        twoSidedExitUpTime X (b + c) ω < barrierRuinTime X a ω
    · have hUD : U < D := hE.mp hN
      rw [if_pos hN]
      simp only [if_pos hB]
      have hNextU :
          twoSidedExitUpTime X (b + c) ω = (u : ℝ≥0∞) + U := by
        simpa only [U, iInf_subtype] using hNext
      rw [if_pos hUD, hNextU]
      have hUFinite : U ≠ ⊤ := ne_top_of_lt (lt_of_lt_of_le hUD le_top)
      have hReal :
          ((u : ℝ≥0∞) + U).toReal = (u : ℝ) + U.toReal := by
        simpa only [ENNReal.coe_toReal] using
          (ENNReal.toReal_add ENNReal.coe_ne_top hUFinite)
      rw [hReal]
      have he : -(q * ((u : ℝ) + U.toReal)) =
          -(q * (u : ℝ)) + -(q * U.toReal) := by ring
      rw [he, Real.exp_add]
      rw [ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _))]
    · have hUD : ¬ U < D := fun hh => hN (hE.mpr hh)
      rw [if_neg hN]
      simp only [if_pos hB]
      rw [if_neg hUD, mul_zero]
  · have hN :
        ¬twoSidedExitUpTime X (b + c) ω < barrierRuinTime X a ω := by
      intro hh
      apply hB
      exact lt_of_le_of_lt
        (twoSidedExitUpTime_mono_threshold X b (b + c)
          (le_add_of_nonneg_right hc.le) ω) hh
    simp only [if_neg hN, if_neg hB]
