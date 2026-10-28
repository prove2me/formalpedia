-- Prove2me | solution 1 for AvramDividend.Classical.firstRecord_capped_namedShiftedReward_markov_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:15:05.104642+00:00
-- url     : https://prove2.me/submissions/288a7cea-541d-4bb6-94ce-53f90ae92026

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_rightCont_stopping_and_clock_measurable
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_survival_in_finiteStoppedHistory
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_survival_measurable_global
import Theorems.Thm_AvramDividend_Classical_finiteStopping_trueShiftedReward_expected_lower

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b : ℝ) (N : ℝ≥0)
    (τ : Ω → ℝ≥0)
    (hτdef : τ = fun ω => (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal)
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (q upper lower : ℝ)
    (ρ σ : Ω → ℝ≥0∞)
    (hρ : ∀ ω, ρ ω =
      ⨅ i : {t : ℝ≥0 // upper < X.X (τ ω + t) ω - X.X (τ ω) ω},
        (i.1 : ℝ≥0∞))
    (hσ : ∀ ω, σ ω =
      ⨅ i : {t : ℝ≥0 // X.X (τ ω + t) ω - X.X (τ ω) ω < lower},
        (i.1 : ℝ≥0∞)) :
    (∫⁻ ω, if twoSidedExitUpTime X b ω < barrierRuinTime X a ω ∧
        twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞) then
      discount (τ ω) else 0 ∂P) *
    (∫⁻ ω, if (⨅ (t : ℝ≥0) (_ : upper < X.X t ω), (t : ℝ≥0∞)) <
                   (⨅ (t : ℝ≥0) (_ : X.X t ω < lower), (t : ℝ≥0∞)) then
       ENNReal.ofReal (Real.exp (-(q *
         ENNReal.toReal (⨅ (t : ℝ≥0) (_ : upper < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) ≤
    (∫⁻ ω, if twoSidedExitUpTime X b ω < barrierRuinTime X a ω ∧
        twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞) then
      discount (τ ω) * (if ρ ω < σ ω then
        ENNReal.ofReal (Real.exp (-(q * (ρ ω).toReal))) else 0)
      else 0 ∂P) := by
  subst τ
  let τc : Ω → ℝ≥0 :=
    fun ω => (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
  let A : Set Ω :=
    {ω : Ω | twoSidedExitUpTime X b ω < barrierRuinTime X a ω} ∩
    {ω : Ω | twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)}
  have hStopAnd := firstRecord_capped_rightCont_stopping_and_clock_measurable X b N
  dsimp only at hStopAnd
  obtain ⟨hStop, hClock⟩ := hStopAnd
  have hHistory :
      MeasurableSet[(isStoppingTime_withTop_of_le_events τc hStop).measurableSpace] A := by
    simpa only [τc, A] using
      (firstRecord_capped_survival_in_finiteStoppedHistory X a b N)
  have hGlobal : MeasurableSet A := by
    simpa only [A] using (firstRecord_capped_survival_measurable_global X a b N)
  have hBound :=
    finiteStopping_trueShiftedReward_expected_lower
      X τc hStop A hHistory hGlobal hClock discount hd q upper lower
  simpa only [hρ, hσ, τc, A, Set.mem_inter_iff, Set.mem_setOf_eq] using hBound
