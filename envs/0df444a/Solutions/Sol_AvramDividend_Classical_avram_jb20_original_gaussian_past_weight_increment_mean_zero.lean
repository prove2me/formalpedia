-- Prove2me | solution 1 for AvramDividend.Classical.avram_jb20_original_gaussian_past_weight_increment_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T17:00:40.302997+00:00
-- url     : https://prove2.me/submissions/75799f31-0204-4618-8400-701c8dca23df

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gb49_predictable_real_condExp_cross_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- A right-continuous-filtration martingale increment has zero mean when
multiplied by an integrable predictable left-endpoint weight. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (R : ℝ≥0 → Ω → ℝ)
    (hRint : ∀ u : ℝ≥0, Integrable (R u) P)
    (hRmart : ∀ u v : ℝ≥0, u ≤ v →
      ∀ᵐ ω ∂P,
        condExp (𝓕.rightCont u) P (R v) ω = R u ω)
    (s t : ℝ≥0) (hst : s ≤ t)
    (H : Ω → ℝ)
    (hH : Measurable[𝓕.rightCont s] H)
    (hProd : Integrable
      (fun ω => H ω * (R t ω - R s ω)) P) :
    (∫ ω, H ω * (R t ω - R s ω) ∂P) = 0 := by
  have hDiffI : Integrable
      (fun ω => R t ω - R s ω) P := by
    exact (hRint t).sub (hRint s)
  have hSub :=
    condExp_sub (hRint t) (hRint s) (𝓕.rightCont s)
  have hDiffCE :
      P[(fun ω => R t ω - R s ω) | 𝓕.rightCont s] =ᵐ[P]
        (fun _ => (0 : ℝ)) := by
    filter_upwards [hSub, hRmart s t hst,
      hRmart s s (le_refl s)] with ω hE hT hS
    change (condExp (𝓕.rightCont s) P (R t - R s)) ω = 0
    rw [hE, Pi.sub_apply, hT, hS, sub_self]
  exact avram_gb49_predictable_real_condExp_cross_zero
    ((𝓕.rightCont).le s) H
    (fun ω => R t ω - R s ω)
    hH hDiffI hProd hDiffCE
