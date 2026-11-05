-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_m_uniqueness_original_unit_moments_inherit_cluster_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:38:11.975208+00:00
-- url     : https://prove2.me/submissions/1a919256-44ad-4e14-b0b2-727e636e563f

import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_cluster_bounded_nonnegative_lintegral_eq

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology BoundedContinuousFunction
open scoped NNReal ENNReal

/-- Along eventually unit-supported original finite measures, the limit of a
monomial lintegral is inherited by every weak cluster point whenever a bounded
continuous NNReal test agrees with that monomial on the unit interval. -/
theorem solution
    {ι : Type*} (l : Filter ι)
    (μi : ι → FiniteMeasure ℝ) (σ : FiniteMeasure ℝ)
    (hcluster : MapClusterPt σ l μi)
    (hunit : ∀ᶠ i in l, (μi i) (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (hσunit : σ (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (g : ℝ →ᵇ ℝ≥0) (k : ℕ)
    (hagree : ∀ z : ℝ, z ∈ Set.Icc (0 : ℝ) 1 →
      (g z : ℝ≥0∞) = (ENNReal.ofReal z) ^ k)
    (a : ℝ≥0∞)
    (hlim : Tendsto (fun i => ∫⁻ z, (ENNReal.ofReal z) ^ k ∂μi i)
      l (nhds a)) :
    (∫⁻ z, (ENNReal.ofReal z) ^ k ∂σ) = a := by
  have htr (μ : FiniteMeasure ℝ)
      (hm : μ (Set.Icc (0 : ℝ) 1)ᶜ = 0) :
      (∫⁻ z, g z ∂μ) = (∫⁻ z, (ENNReal.ofReal z) ^ k ∂μ) := by
    have hs : ∀ᵐ z ∂(μ : Measure ℝ), z ∈ Set.Icc (0 : ℝ) 1 :=
      (mem_ae_iff).2 ((FiniteMeasure.null_iff_toMeasure_null μ _).1 hm)
    apply lintegral_congr_ae
    filter_upwards [hs] with z hz
    exact hagree z hz
  have hev :
      (fun i => ∫⁻ z, g z ∂μi i) =ᶠ[l]
        (fun i => ∫⁻ z, (ENNReal.ofReal z) ^ k ∂μi i) :=
    hunit.mono (fun i hi => htr (μi i) hi)
  have htest : Tendsto (fun i => ∫⁻ z, g z ∂μi i) l (nhds a) :=
    hlim.congr' hev.symm
  calc
    (∫⁻ z, (ENNReal.ofReal z) ^ k ∂σ) = (∫⁻ z, g z ∂σ) :=
      (htr σ hσunit).symm
    _ = a :=
      AvramDividend.Classical.avram_p2_m_uniqueness_cluster_bounded_nonnegative_lintegral_eq
        l μi σ hcluster g a htest
