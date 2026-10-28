-- Prove2me | solution 1 for AvramDividend.Classical.chat12_capped_record_next_expected_ge_current_mul_twoSided
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:23:19.516944+00:00
-- url     : https://prove2.me/submissions/383adb08-7859-48e4-86c3-059d2383bca7

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Data.ENNReal.Basic
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_finiteStopping_trueTwoSided_expected_lower_imported
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_rightCont_stopping_and_clock_measurable
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_survival_in_finiteStoppedHistory
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_survival_measurable_global
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_clock_eq_true_clock_within_horizon
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_value_eq_threshold
import Theorems.Thm_AvramDividend_Classical_killed_nextRecord_weight_ge_countable_twoSided_reward

set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
set_option pp.explicit false
set_option pp.fullNames false

/-- Finite-cap killed record renewal expectation without scale-function assumptions. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q a b ε : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 < ε)
    (N : ℝ≥0) :
    (∫⁻ ω, if
      (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
      (⨅ (t : ℝ≥0) (_ : X.X t ω < ε - a), (t : ℝ≥0∞)) then
      ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
        (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) *
    (∫⁻ ω, if twoSidedExitUpTime X b ω < barrierRuinTime X a ω ∧
      twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞) then
      ENNReal.ofReal (ε * Real.exp (-(q * (twoSidedExitUpTime X b ω).toReal)))
      else 0 ∂P) ≤
    (∫⁻ ω, if twoSidedExitUpTime X (b + ε) ω < barrierRuinTime X a ω then
      ENNReal.ofReal (ε * Real.exp (-(q * (twoSidedExitUpTime X (b + ε) ω).toReal)))
      else 0 ∂P) := by
  classical
  let factor : ℝ≥0∞ := ∫⁻ ω, if
      (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
      (⨅ (t : ℝ≥0) (_ : X.X t ω < ε - a), (t : ℝ≥0∞)) then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
          (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P
  let next : ℝ≥0∞ := ∫⁻ ω, if twoSidedExitUpTime X (b + ε) ω <
      barrierRuinTime X a ω then
      ENNReal.ofReal (ε * Real.exp (-(q * (twoSidedExitUpTime X (b + ε) ω).toReal)))
      else 0 ∂P
  let oldCap (N : ℝ≥0) : ℝ≥0∞ :=
    ∫⁻ ω, if twoSidedExitUpTime X b ω < barrierRuinTime X a ω ∧
          twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞) then
      ENNReal.ofReal (ε * Real.exp (-(q * (twoSidedExitUpTime X b ω).toReal)))
      else 0 ∂P
  let τ : Ω → ℝ≥0 := fun ω => (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
  let A : Set Ω := {ω | twoSidedExitUpTime X b ω < barrierRuinTime X a ω} ∩ {ω | twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)}
  let discount : ℝ≥0 → ℝ≥0∞ := fun t => ENNReal.ofReal ε * ENNReal.ofReal (Real.exp (-(q * (t : ℝ))))
  let weight : Ω → ℝ≥0∞ := fun ω =>
    if twoSidedExitUpTime X (b + ε) ω < barrierRuinTime X a ω then
      ENNReal.ofReal (ε * Real.exp
        (-(q * (twoSidedExitUpTime X (b + ε) ω).toReal)))
    else 0
  have hτboth := firstRecord_capped_rightCont_stopping_and_clock_measurable X b N
  have hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s} := hτboth.1
  have hτfine : Measurable τ := hτboth.2
  have hA : MeasurableSet[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] A := by simpa only [A, τ] using firstRecord_capped_survival_in_finiteStoppedHistory X a b N
  have hAfine : MeasurableSet A := by simpa only [A] using firstRecord_capped_survival_measurable_global X a b N
  have hd : Measurable discount := by dsimp [discount]; fun_prop
  have hMarkov := finiteStopping_trueTwoSided_expected_lower_imported
    X τ hτ A hA hAfine hτfine discount hd q ε (ε - a) weight (by
      intro ω
      by_cases hω : ω ∈ A
      · have hclock : τ ω = (twoSidedExitUpTime X b ω).toNNReal := firstRecord_capped_clock_eq_true_clock_within_horizon X b N ω hω.2
        have hfinite : twoSidedExitUpTime X b ω ≠ ⊤ := ne_top_of_le_ne_top (by simp) hω.2
        have hu : (((twoSidedExitUpTime X b ω).toNNReal : ℝ≥0) : ℝ≥0∞) =
            twoSidedExitUpTime X b ω := ENNReal.coe_toNNReal hfinite
        have hAt : X.X (twoSidedExitUpTime X b ω).toNNReal ω = b := by
          apply firstUpcrossing_value_eq_threshold X b hb ω _
          simpa only [twoSidedExitUpTime] using hu
        have hPath := killed_nextRecord_weight_ge_countable_twoSided_reward
          X a b ε q ha hb hε.le ω (twoSidedExitUpTime X b ω).toNNReal
          hu hAt (by rw [hu]; exact hω.1)
        simpa [weight, discount, hω, hclock, mul_assoc] using hPath
      · simp [hω, weight]
    )
  let past : Ω → ℝ≥0∞ := fun ω =>
    @ite ℝ≥0∞ (ω ∈ A) (Classical.propDecidable (ω ∈ A))
      (discount (τ ω)) 0
  have hPrev : oldCap N ≤ (∫⁻ ω, past ω ∂P) := by
    apply lintegral_mono
    intro ω
    by_cases hω : ω ∈ A
    · have hclock := firstRecord_capped_clock_eq_true_clock_within_horizon X b N ω hω.2
      have hs : twoSidedExitUpTime X b ω < barrierRuinTime X a ω := hω.1
      have hN : twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞) := hω.2
      simpa [past, A, oldCap, discount, τ, hω, hs, hN,
        min_eq_left hN, ENNReal.ofReal_mul hε.le,
        ENNReal.coe_toNNReal_eq_toReal]
    · have hnot : ¬ (twoSidedExitUpTime X b ω < barrierRuinTime X a ω ∧
          twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)) := by
        simpa only [A, Set.mem_inter_iff, Set.mem_setOf_eq] using hω
      simp [past, A, oldCap, hω, hnot]
  have hMarkovPast : (∫⁻ ω, past ω ∂P) * factor ≤ next := by
    simpa only [past, factor, next, weight] using hMarkov
  have hGoal : factor * oldCap N ≤ next := by
    calc
      factor * oldCap N ≤ factor * (∫⁻ ω, past ω ∂P) := by gcongr
      _ = (∫⁻ ω, past ω ∂P) * factor := mul_comm _ _
      _ ≤ next := hMarkovPast
  simpa only [factor, oldCap, next] using hGoal
