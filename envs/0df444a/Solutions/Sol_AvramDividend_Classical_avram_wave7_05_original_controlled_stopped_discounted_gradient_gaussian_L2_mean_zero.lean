-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_original_controlled_stopped_discounted_gradient_gaussian_L2_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T14:52:03.809093+00:00
-- url     : https://prove2.me/submissions/07383b4c-6f34-42dd-9d01-a716c5b8844d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_source_stopped_discounted_deriv_predictable
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_stopped_gaussian_bounded_predictable_gain_L2_mean_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q : ℝ) (T : ℝ≥0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (B : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ B)
    (h : ℝ≥0) (K : ℝ) (hK : 0 ≤ K)
    (hHbound : ∀ ω : Ω, |(stoppedValue (fun t ω =>
        if t ≤ T then
          (Real.exp (-(q * (t : ℝ))) *
            deriv w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
          (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
        else 0) (fun ω => (τ ω : WithTop ℝ≥0))) ω| ≤ K) :
    let H : Ω → ℝ := stoppedValue (fun t ω =>
        if t ≤ T then
          (Real.exp (-(q * (t : ℝ))) *
            deriv w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
          (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
        else 0) (fun ω => (τ ω : WithTop ℝ≥0))
    let Y : Ω → ℝ := fun ω =>
        X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
    MemLp (fun ω => H ω * Y ω) 2 P ∧
      Integrable (fun ω => H ω * Y ω) P ∧
        (∫ ω, H ω * Y ω ∂P) = 0 := by
  let H : Ω → ℝ := stoppedValue (fun t ω =>
        if t ≤ T then
          (Real.exp (-(q * (t : ℝ))) *
            deriv w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
          (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
        else 0) (fun ω => (τ ω : WithTop ℝ≥0))
  let Y : Ω → ℝ := fun ω =>
        X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
  have hstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)) :=
    isStoppingTime_withTop_of_le_events τ hτ
  have hHstop : Measurable[hstop.measurableSpace] H :=
    measurable_stoppedValue
      ((avram_wave3_04_source_stopped_discounted_deriv_predictable
        X x D hD w q T).isStronglyProgressive) hstop
  have hHg : Measurable H :=
    hHstop.mono hstop.measurableSpace_le le_rfl
  have hOne :=
    avram_wave7_05_original_stopped_gaussian_bounded_predictable_gain_L2_mean_zero
      X hν τ hτ B hbounded h H hHstop hHg K hK hHbound
  dsimp only at hOne
  change MemLp (fun ω => H ω * Y ω) 2 P ∧
    Integrable (fun ω => H ω * Y ω) P ∧
      (∫ ω, H ω * Y ω ∂P) = 0
  exact hOne
