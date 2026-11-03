-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_original_stopped_gaussian_bounded_predictable_gain_L2_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T14:24:03.512489+00:00
-- url     : https://prove2.me/submissions/a3ec5d6f-f8af-4129-b403-97b2705179cf

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_weighted_true_increment_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_history_weighted_condExp_zero

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
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (G : Ω → ℝ)
    (hGstop : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] G)
    (hGglobal : Measurable G)
    (K : ℝ) (hK : 0 ≤ K) (hGbound : ∀ ω, |G ω| ≤ K) :
    let Y : Ω → ℝ := fun ω =>
      X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
    MemLp (fun ω => G ω * Y ω) 2 P ∧
      Integrable (fun ω => G ω * Y ω) P ∧
        (∫ ω, G ω * Y ω ∂P) = 0 := by
  classical
  dsimp only
  letI : IsProbabilityMeasure P := X.isProbability
  have hLp :
      MemLp (fun ω =>
        G ω * (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c)) 2 P :=
    avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_weighted_true_increment_MemLp_two
      X hν τ (isStoppingTime_withTop_of_le_events τ hτ)
        T hbounded h G hGglobal.stronglyMeasurable K hK hGbound
  have hGI :
      Integrable (fun ω =>
        G ω * (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c)) P :=
    hLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hCE :
      P[(fun ω => G ω *
        (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c)) |
        (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
        =ᵐ[P] (fun _ => (0 : ℝ)) :=
    avram_wave6_03_original_rightCont_stopped_gaussian_history_weighted_condExp_zero
      X hν τ hτ T hbounded h G hGstop hGI
  have hIntegralEq :
      (∫ ω, (P[(fun ω => G ω *
        (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c)) |
        (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]) ω ∂P) =
      ∫ ω, G ω *
        (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ∂P :=
    integral_condExp (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace_le
  refine ⟨hLp, hGI, ?_⟩
  calc
    (∫ ω, G ω *
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ∂P) =
      ∫ ω, (P[(fun ω => G ω *
        (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c)) |
        (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]) ω ∂P :=
      hIntegralEq.symm
    _ = ∫ ω, (0 : ℝ) ∂P := integral_congr_ae hCE
    _ = 0 := by simp
