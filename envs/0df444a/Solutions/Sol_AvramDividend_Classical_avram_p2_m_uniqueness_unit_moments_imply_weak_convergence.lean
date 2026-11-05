-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_m_uniqueness_unit_moments_imply_weak_convergence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:58:12.767772+00:00
-- url     : https://prove2.me/submissions/ead00e51-4c6a-47f3-871e-1ab17a72ef3e

import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_clamped_unit_nnreal_bounded_continuous
import Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_original_unit_moments_inherit_cluster_limit
import Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_eventually_unit_finite_measure_tendsto_of_unique_cluster
import Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_finite_real_unit_moments_no_regular_assumptions

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology BoundedContinuousFunction
open scoped NNReal ENNReal

/-- Eventual unit support, an eventual mass bound, and convergence of genuine
monomial moments determine the full weak limit of finite original measures. -/
theorem solution
    {ι : Type*} (l : Filter ι)
    (C : ℝ≥0) (μi : ι → FiniteMeasure ℝ) (ρ : FiniteMeasure ℝ)
    (hmass : ∀ᶠ i in l, (μi i).mass ≤ C)
    (hunit : ∀ᶠ i in l, (μi i) (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (hρunit : ρ (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (hmom : ∀ k : ℕ,
      Tendsto (fun i => ∫⁻ z, (ENNReal.ofReal z) ^ k ∂μi i) l
        (nhds (∫⁻ z, (ENNReal.ofReal z) ^ k ∂ρ))) :
    Tendsto μi l (nhds ρ) := by
  apply AvramDividend.Classical.avram_p2_m_uniqueness_eventually_unit_finite_measure_tendsto_of_unique_cluster
    l C μi ρ hmass hunit
  intro σ hσmass hσunit hcluster
  obtain ⟨f, hfle, hf⟩ :=
    AvramDividend.Classical.avram_p2_m_uniqueness_clamped_unit_nnreal_bounded_continuous
  have hpow (k : ℕ) : ∀ z : ℝ, z ∈ Set.Icc (0 : ℝ) 1 →
      ((f ^ k) z : ℝ≥0∞) = (ENNReal.ofReal z) ^ k := by
    intro z hz
    rw [BoundedContinuousFunction.pow_apply, ENNReal.coe_pow, hf z hz]
  have hmomσ (k : ℕ) :
      (∫⁻ z, (ENNReal.ofReal z) ^ k ∂σ) =
        (∫⁻ z, (ENNReal.ofReal z) ^ k ∂ρ) :=
    AvramDividend.Classical.avram_p2_m_uniqueness_original_unit_moments_inherit_cluster_limit
      l μi σ hcluster hunit hσunit (f ^ k) k (hpow k) _ (hmom k)
  apply FiniteMeasure.toMeasure_injective
  apply AvramDividend.Classical.avram_p2_m_uniqueness_finite_real_unit_moments_no_regular_assumptions
    (σ : Measure ℝ) (ρ : Measure ℝ)
  · exact (mem_ae_iff).2 ((FiniteMeasure.null_iff_toMeasure_null σ _).1 hσunit)
  · exact (mem_ae_iff).2 ((FiniteMeasure.null_iff_toMeasure_null ρ _).1 hρunit)
  · exact hmomσ
