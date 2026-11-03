-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_gaussian_predictable_compensated_quadratic_condExp_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T07:04:15.739377+00:00
-- url     : https://prove2.me/submissions/81edc60b-2fe5-4fc5-96f8-0e5877bde128

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_history_weighted_condExp_quadratic_drift

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original stopped weighted Gaussian quadratic residual is a conditional martingale difference. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (B : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ B)
    (h : ℝ≥0) (H : Ω → ℝ)
    (hH : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] H)
    (hHI : Integrable H P)
    (hProdI : Integrable (fun ω =>
      H ω * (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2) P) :
    P[(fun ω =>
      H ω * (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2 -
      ((h : ℝ) * X.σ ^ 2) * H ω) |
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
      =ᵐ[P] (fun _ => (0 : ℝ)) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)) :=
    isStoppingTime_withTop_of_le_events τ hτ
  let Y : Ω → ℝ := fun ω =>
    X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
  let F : Ω → ℝ := fun ω => H ω * Y ω ^ 2
  let G : Ω → ℝ := fun ω => ((h : ℝ) * X.σ ^ 2) * H ω
  have hFI : Integrable F P := hProdI
  have hGI : Integrable G P := hHI.const_mul _
  have hGstop : Measurable[hτstop.measurableSpace] G :=
    measurable_const.mul hH
  have hCG : P[G | hτstop.measurableSpace] = G :=
    condExp_of_stronglyMeasurable
      hτstop.measurableSpace_le hGstop.stronglyMeasurable hGI
  have hCF :=
    avram_wave6_03_original_rightCont_stopped_gaussian_history_weighted_condExp_quadratic_drift
      X hν τ hτ B hbounded h H hH hProdI
  change P[F | hτstop.measurableSpace] =ᵐ[P] G at hCF
  have hSub :=
    condExp_sub hFI hGI hτstop.measurableSpace
  change P[F - G | hτstop.measurableSpace] =ᵐ[P]
    P[F | hτstop.measurableSpace] - P[G | hτstop.measurableSpace] at hSub
  change P[F - G | hτstop.measurableSpace] =ᵐ[P] (fun _ => (0 : ℝ))
  filter_upwards [hSub, hCF] with ω hs hf
  calc
    (P[F - G | hτstop.measurableSpace]) ω =
        (P[F | hτstop.measurableSpace] - P[G | hτstop.measurableSpace]) ω := hs
    _ = (P[F | hτstop.measurableSpace]) ω - G ω := by rw [hCG]; rfl
    _ = 0 := by rw [hf]; ring
