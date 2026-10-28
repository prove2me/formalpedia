-- Prove2me | solution 1 for AvramDividend.Classical.chat12_firstRecord_geometric_trueExit_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:49:57.434652+00:00
-- url     : https://prove2.me/submissions/61cc13fe-aa3b-44ed-a8a8-947c1e560e30

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.GCongr
import Theorems.Thm_AvramDividend_Classical_chat12_killed_firstRecord_next_expected_ge_current_mul_twoSided

import Theorems.Thm_AvramDividend_Classical_chat12_initial_record_trueExit_factor_lower
import Theorems.Thm_AvramDividend_Classical_chat12_firstRecord_geometric_trueFactor_of_base

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∀ n : ℕ, ENNReal.ofReal ε * (∫⁻ ω, if
        (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
        (⨅ (t : ℝ≥0) (_ : X.X t ω < ε - a), (t : ℝ≥0∞)) then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
          (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) ^ (n + 1) ≤
      (∫⁻ ω, if twoSidedExitUpTime X ((((n + 1 : ℕ)) : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X ((((n + 1 : ℕ)) : ℝ) * ε) ω).toReal)))
      else 0 ∂P) := by
  have hbase : ENNReal.ofReal ε * (∫⁻ ω, if
        (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
        (⨅ (t : ℝ≥0) (_ : X.X t ω < ε - a), (t : ℝ≥0∞)) then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
          (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) ≤
      (∫⁻ ω, if twoSidedExitUpTime X ((1 : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X ((1 : ℝ) * ε) ω).toReal)))
      else 0 ∂P) := by
    have hNamed :=
      chat12_initial_record_trueExit_factor_lower X q a ε ha hε
    have hClockIntegral :
        (∫⁻ ω, if twoSidedExitUpTime X ε ω <
            twoSidedExitDownTime X (ε - a) ω then
          ENNReal.ofReal (Real.exp
            (-(q * (twoSidedExitUpTime X ε ω).toReal)))
        else 0 ∂P) =
        (∫⁻ ω, if
          (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < ε - a), (t : ℝ≥0∞)) then
          ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
        else 0 ∂P) := by
      apply lintegral_congr
      intro ω
      by_cases hω :
          (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < ε - a), (t : ℝ≥0∞))
      · have hNamedEvent :
            twoSidedExitUpTime X ε ω <
              twoSidedExitDownTime X (ε - a) ω := by
          simpa only [twoSidedExitUpTime, twoSidedExitDownTime] using hω
        simp only [if_pos hNamedEvent, if_pos hω]
        rfl
      · have hNamedEvent :
            ¬ (twoSidedExitUpTime X ε ω <
              twoSidedExitDownTime X (ε - a) ω) := by
          simpa only [twoSidedExitUpTime, twoSidedExitDownTime] using hω
        simp only [if_neg hNamedEvent, if_neg hω]
    calc
      _ = ENNReal.ofReal ε *
          (∫⁻ ω, if twoSidedExitUpTime X ε ω <
              twoSidedExitDownTime X (ε - a) ω then
            ENNReal.ofReal (Real.exp
              (-(q * (twoSidedExitUpTime X ε ω).toReal)))
          else 0 ∂P) := by rw [hClockIntegral]
      _ ≤ _ := hNamed
  exact chat12_firstRecord_geometric_trueFactor_of_base X q a ε ha hε hbase
