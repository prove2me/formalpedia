-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_m_uniqueness_original_eventual_moments_force_weak_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:09:36.268776+00:00
-- url     : https://prove2.me/submissions/45ac20c9-82d8-4504-9f14-4014b435c310

import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_eventual_original_measure_finite_lift
import Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_unit_moments_imply_weak_convergence

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- The original (not necessarily finite at exceptional indices) laws inherit
weak convergence from their actual monomial limits via an eventual finite lift. -/
theorem solution
    {ι : Type*} (l : Filter ι)
    (μi : ι → Measure ℝ) (C : ℝ≥0∞) (hC : C < ⊤)
    (hmass : ∀ᶠ i in l, (μi i) Set.univ ≤ C)
    (hunit : ∀ᶠ i in l, ∀ᵐ z ∂μi i, z ∈ Set.Icc (0 : ℝ) 1)
    (ρ : FiniteMeasure ℝ)
    (hρunit : ρ (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (hmom : ∀ k : ℕ,
      Tendsto (fun i => ∫⁻ z, (ENNReal.ofReal z) ^ k ∂μi i) l
        (nhds (∫⁻ z, (ENNReal.ofReal z) ^ k ∂ρ))) :
    ∃ νi : ι → FiniteMeasure ℝ,
      (∀ᶠ i in l, (νi i : Measure ℝ) = μi i) ∧
      Tendsto νi l (nhds ρ) := by
  obtain ⟨νi, hev⟩ :=
    AvramDividend.Classical.avram_p2_m_uniqueness_eventual_original_measure_finite_lift
      l μi C hC hmass hunit
  refine ⟨νi, hev.mono (fun i hi => hi.1), ?_⟩
  apply AvramDividend.Classical.avram_p2_m_uniqueness_unit_moments_imply_weak_convergence
    l C.toNNReal νi ρ
  · exact hev.mono (fun i hi => hi.2.1)
  · exact hev.mono (fun i hi => hi.2.2)
  · exact hρunit
  · intro k
    apply (hmom k).congr'
    exact hev.mono (fun i hi => by
      change (∫⁻ z, (ENNReal.ofReal z) ^ k ∂μi i) =
        (∫⁻ z, (ENNReal.ofReal z) ^ k ∂(νi i : Measure ℝ))
      rw [← hi.1])
