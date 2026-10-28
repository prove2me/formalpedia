-- Prove2me | solution 1 for AvramDividend.Classical.chat04_actual_exponential_clock_mixed_borel_event_reversal_ws01a
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T13:39:57.071868+00:00
-- url     : https://prove2.me/submissions/f6baabc0-7a38-4084-a703-8c212aa8daf7

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat04_actual_exponential_clock_terminal_weighted_drawdown_law_ws01a
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (r : ℝ) (hr : 0 < r) (c : ℝ)
    (A : Set ℝ) (hA : MeasurableSet A) :
    (P.prod (expMeasure r))
      {z : Ω × ℝ |
        runningSup X z.2.toNNReal z.1 -
            X.X z.2.toNNReal z.1 ∈ A ∧
        X.X z.2.toNNReal z.1 - X.X 0 z.1 < c} =
    (P.prod (expMeasure r))
      {z : Ω × ℝ |
        X.X 0 z.1 +
            -sInf {y : ℝ | ∃ s : ℝ≥0,
              s ≤ z.2.toNNReal ∧ y = X.X s z.1} ∈ A ∧
        X.X z.2.toNNReal z.1 - X.X 0 z.1 < c} := by
  classical
  let T : Ω × ℝ → ℝ := fun z => X.X z.2.toNNReal z.1
  let Z : Ω × ℝ → ℝ := fun z => T z - X.X 0 z.1
  let ρ : Ω × ℝ → ℝ≥0∞ := fun z => if Z z < c then 1 else 0
  let μ : Measure (Ω × ℝ) := P.prod (expMeasure r)
  let D : Ω × ℝ → ℝ := fun z =>
    runningSup X z.2.toNNReal z.1 - T z
  let L : Ω × ℝ → ℝ := fun z =>
    X.X 0 z.1 +
      -sInf {y : ℝ | ∃ s : ℝ≥0,
        s ≤ z.2.toNNReal ∧ y = X.X s z.1}
  let C : Set (Ω × ℝ) := {z | Z z < c}
  have hTri := levy_exponential_real_clock_extrema_drawdown_measurable X
  have hD : Measurable D := by simpa only [D, T] using hTri.snd
  have hX0 : Measurable (fun z : Ω × ℝ => X.X 0 z.1) :=
    (X.adapted.measurable).comp measurable_fst
  have hL : Measurable L := hX0.add (by simpa only [] using hTri.fst.snd)
  have hT : Measurable T :=
    (chat04_levy_joint_time_state_measurable X).comp
      ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst)
  have hZ : Measurable Z := hT.sub hX0
  have hC : MeasurableSet C := measurableSet_Iio.preimage hZ
  have hD_A : MeasurableSet (D ⁻¹' A) := hA.preimage hD
  have hL_A : MeasurableSet (L ⁻¹' A) := hA.preimage hL
  have hRestr (E : Set (Ω × ℝ)) (hE : MeasurableSet E) :
      (μ.withDensity ρ) E = μ (E ∩ C) := by
    rw [withDensity_apply ρ hE, ← lintegral_indicator hE ρ]
    have hfun :
        E.indicator ρ = (E ∩ C).indicator (fun _ => (1 : ℝ≥0∞)) := by
      funext z
      by_cases he : z ∈ E
      · by_cases hc : z ∈ C
        · have hz : Z z < c := hc
          simp [Set.indicator_of_mem, he, hc, C, ρ, hz]
        · have hz : ¬ Z z < c := hc
          simp [Set.indicator_of_mem, Set.indicator_of_notMem, he, hc, C, ρ, hz]
      · simp [Set.indicator_of_notMem, he, C, ρ]
    rw [hfun, lintegral_indicator (hE.inter hC)]
    simp
  have hWeighted := chat04_actual_exponential_clock_terminal_weighted_drawdown_law_ws01a
    X r hr c
  have hAeq :
      (μ.withDensity ρ) (D ⁻¹' A) =
      (μ.withDensity ρ) (L ⁻¹' A) := by
    have h := congrArg (fun ν : Measure ℝ => ν A) hWeighted
    change ((μ.withDensity ρ).map D) A =
      ((μ.withDensity ρ).map L) A at h
    rw [Measure.map_apply hD hA, Measure.map_apply hL hA] at h
    exact h
  rw [hRestr (D ⁻¹' A) hD_A, hRestr (L ⁻¹' A) hL_A] at hAeq
  change μ {z : Ω × ℝ | D z ∈ A ∧ Z z < c} =
    μ {z : Ω × ℝ | L z ∈ A ∧ Z z < c} at hAeq
  exact hAeq
