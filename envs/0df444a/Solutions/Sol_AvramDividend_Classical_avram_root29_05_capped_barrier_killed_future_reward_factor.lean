-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_05_capped_barrier_killed_future_reward_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T08:11:41.046986+00:00
-- url     : https://prove2.me/submissions/bf7fe188-7b1a-4c78-837a-89d09500adbb

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_isDividendStrategy_nonnegative_barrier
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_upperPassage_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_upperPassage_capped_stopping_rightCont
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_coe_toNNReal_with_measure_import
import Theorems.Thm_AvramDividend_Classical_barrierSuccessfulClockCutoff_stoppedHistory
import Theorems.Thm_AvramDividend_Classical_stoppedHistory_measurable_of_equal_finite_clocks
import Theorems.Thm_AvramDividend_Classical_stoppedHistory_event_measurable
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_killedDiscount_futureReward_factor_rightCont

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The genuine first-upcrossing prefix, killed by the controlled barrier
ruin time and capped at N, factors from an arbitrary measurable future reward.
This supplies the stopped-history premise needed for dividend renewal. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hx : 0 ≤ x) (ha : 0 < a) (hxa : x ≤ a)
    (N : ℝ≥0)
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (reward : (ℝ≥0 → ℝ) → ℝ≥0∞) (hr : Measurable reward) :
    let T := twoSidedExitUpTime X (a - x)
    let R := ruinTime X x (barrierStrategy X x a)
    let τ : Ω → ℝ≥0 := fun ω => (min (T ω) (N : ℝ≥0∞)).toNNReal
    let A : Set Ω := {ω | T ω < R ω ∧ T ω ≤ (N : ℝ≥0∞)}
    (∫⁻ ω, if ω ∈ A then
        discount (τ ω) *
          reward (fun t : ℝ≥0 => X.X (τ ω + t) ω - X.X (τ ω) ω)
      else 0 ∂P) =
      (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
        (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P) := by
  classical
  let T : Ω → ℝ≥0∞ := twoSidedExitUpTime X (a - x)
  let R : Ω → ℝ≥0∞ := ruinTime X x (barrierStrategy X x a)
  let τ : Ω → ℝ≥0 := fun ω => (min (T ω) (N : ℝ≥0∞)).toNNReal
  let A : Set Ω := {ω | T ω < R ω ∧ T ω ≤ (N : ℝ≥0∞)}
  have hU : IsStoppingTime 𝓕.rightCont T :=
    upperPassage_stopping_rightCont_filtration X (a - x)
  have hD : IsDividendStrategy 𝓕 (barrierStrategy X x a) :=
    barrierStrategy_isDividendStrategy_nonnegative_barrier X x a hx ha.le
  have hR : IsStoppingTime 𝓕.rightCont R :=
    ruinTime_stopping_rightCont_filtration X x _ hD
  have hCap : IsStoppingTime 𝓕.rightCont
      (fun ω => min (T ω) (N : ℝ≥0∞)) :=
    upperPassage_capped_stopping_rightCont X (a - x) N
  have hEq (ω : Ω) : (τ ω : ℝ≥0∞) =
      min (T ω) (N : ℝ≥0∞) :=
    firstRecord_capped_coe_toNNReal_with_measure_import X (a - x) N ω
  have hτ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s} := by
    intro s
    have hs : {ω : Ω | τ ω ≤ s} =
        {ω : Ω | min (T ω) (N : ℝ≥0∞) ≤ (s : ℝ≥0∞)} := by
      ext ω
      simp only [mem_setOf_eq]
      rw [← hEq ω]
      exact ENNReal.coe_le_coe.symm
    rw [hs]
    exact hCap s
  have hAτ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] (A ∩ {ω | τ ω ≤ s}) := by
    intro s
    have hs : (A ∩ {ω | τ ω ≤ s}) =
        (({ω | T ω < R ω} ∩ {ω | T ω ≤ (N : ℝ≥0∞)}) ∩
          {ω | min (T ω) (N : ℝ≥0∞) ≤ (s : ℝ≥0∞)}) := by
      ext ω
      simp only [A, mem_inter_iff, mem_setOf_eq]
      rw [← hEq ω]
      simp only [ENNReal.coe_le_coe]
    rw [hs]
    exact barrierSuccessfulClockCutoff_stoppedHistory T R hU hR N s
  have hAfine : MeasurableSet A :=
    stoppedHistory_event_measurable τ A hAτ
  have hτleN (ω : Ω) : τ ω ≤ N := by
    have hb : (τ ω : ℝ≥0∞) ≤ (N : ℝ≥0∞) := by
      rw [hEq ω]
      exact min_le_right _ _
    exact ENNReal.coe_le_coe.mp hb
  have hAN : MeasurableSet[𝓕.rightCont N] A := by
    have hset : A ∩ {ω | τ ω ≤ N} = A := by
      ext ω
      simp only [mem_inter_iff, mem_setOf_eq, hτleN ω, and_true]
    have h := hAτ N
    rw [hset] at h
    exact h
  have hASup : MeasurableSet[
      ⨆ s : ℝ≥0, (𝓕.rightCont s : MeasurableSpace Ω)] A := by
    exact (le_iSup (fun s : ℝ≥0 =>
      (𝓕.rightCont s : MeasurableSpace Ω)) N) A hAN
  have hA_cap : MeasurableSet[hCap.measurableSpace] A := by
    rw [hCap.measurableSet]
    refine ⟨hASup, ?_⟩
    intro s
    change MeasurableSet[𝓕.rightCont s]
      (({ω | T ω < R ω} ∩ {ω | T ω ≤ (N : ℝ≥0∞)}) ∩
        {ω | min (T ω) (N : ℝ≥0∞) ≤ (s : ℝ≥0∞)})
    exact barrierSuccessfulClockCutoff_stoppedHistory T R hU hR N s
  have hA : MeasurableSet[
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] A :=
    stoppedHistory_measurable_of_equal_finite_clocks τ hτ _ hCap hEq A hA_cap
  have hτfine : Measurable τ := by
    change Measurable (fun ω =>
      ENNReal.toNNReal (min (T ω) (N : ℝ≥0∞)))
    exact ENNReal.measurable_toNNReal.comp
      (hCap.measurable.mono hCap.measurableSpace_le le_rfl)
  change (∫⁻ ω, if ω ∈ A then discount (τ ω) *
      reward (fun t : ℝ≥0 => X.X (τ ω + t) ω - X.X (τ ω) ω)
    else 0 ∂P) =
    (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
      (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P)
  have hfactor :=
    levy_finiteStopping_killedDiscount_futureReward_factor_rightCont
      X τ hτ A hA hAfine hτfine discount hd reward hr
  convert hfactor using 1
  · apply lintegral_congr
    intro ω
    by_cases hω : ω ∈ A
    · simp only [if_pos hω]
    · simp only [if_neg hω]
  · congr 1
    apply lintegral_congr
    intro ω
    by_cases hω : ω ∈ A
    · simp only [if_pos hω]
    · simp only [if_neg hω]
