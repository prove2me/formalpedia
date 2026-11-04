-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_finite_window_source_jump_generator_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:21:42.631059+00:00
-- url     : https://prove2.me/submissions/c0b37186-7b40-41b6-9b1b-c6cc4501db3e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_source_interval_generator_alignment
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_single_mean_zero_horizon_gives_all_prior_jump_decomposition

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- One first-moment normalisation supplies source physical-generator alignment
and exact intrinsic-jump increment decomposition over all subintervals of T. -/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (T : ℝ≥0)
    (hIntegrable : Integrable (fun ω : Ω =>
      ((T : ℝ) * X.drift - X.X T ω) -
        (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ T then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal) P)
    (hMeanZero : (∫ ω : Ω,
      (((T : ℝ) * X.drift - X.X T ω) -
        (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ T then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal) ∂P) = 0)
    (w : ℝ → ℝ) (x : ℝ) (hGen : X.GeneratorIntegrable w x) :
    (X.generator w x = X.drift * deriv w x +
      ∫ y in Iio (0 : ℝ), w (x + y) - w x ∂X.ν) ∧
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, s ≤ t → t ≤ T →
      X.X t ω - X.X s ω =
        ((t : ℝ) - (s : ℝ)) * X.drift -
        (∫⁻ p,
          (if s < p.1 ∧ p.1 ≤ t then ENNReal.ofReal (-p.2) else 0) ∂
          ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
            X.X u ω - Function.leftLim
              (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u)))).toReal := by
  have hboth :=
    avram_p3_a_bvdrift_source_interval_generator_alignment X hBV w x hGen
  refine ⟨hboth.1, ?_⟩
  have hprefix :=
    avram_p3_a_bvdrift_single_mean_zero_horizon_gives_all_prior_jump_decomposition
      X hStanding hBV T hIntegrable hMeanZero
  filter_upwards [hboth.2, hprefix] with ω hω hprefixω
  obtain ⟨R, _hRdef, hR0, hRmono, hRnonneg, hinterval⟩ := hω
  have hRT : R T = 0 := by
    have h0T := hinterval 0 T (by positivity)
    have hT := hprefixω T le_rfl
    simp only [NNReal.coe_zero, zero_sub, sub_zero] at h0T
    rw [X.X_zero ω, hR0] at h0T
    simp only [sub_zero] at h0T
    linarith only [h0T, hT]
  intro s t hst htT
  have hs : R s = 0 := by
    have hnonneg := hRnonneg s
    have hle := hRmono ((hst.trans htT))
    linarith only [hnonneg, hle, hRT]
  have ht : R t = 0 := by
    have hnonneg := hRnonneg t
    have hle := hRmono htT
    linarith only [hnonneg, hle, hRT]
  simpa [hs, ht] using hinterval s t hst
