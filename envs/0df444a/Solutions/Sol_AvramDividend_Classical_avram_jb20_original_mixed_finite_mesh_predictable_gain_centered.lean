-- Prove2me | solution 1 for AvramDividend.Classical.avram_jb20_original_mixed_finite_mesh_predictable_gain_centered
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T17:26:23.35971+00:00
-- url     : https://prove2.me/submissions/dfb7214f-5d87-4c94-9612-200f4ee85c0f

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_jb20_original_gaussian_finite_mesh_predictable_gain_centered
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Both physical predictable noise channels have integrable centred finite mesh gain. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {ι : Type*} (S : Finset ι)
    (R J : ℝ≥0 → Ω → ℝ)
    (hRint : ∀ u : ℝ≥0, Integrable (R u) P)
    (hRmart : ∀ u v : ℝ≥0, u ≤ v →
      ∀ᵐ ω ∂P, condExp (𝓕.rightCont u) P (R v) ω = R u ω)
    (hJint : ∀ u : ℝ≥0, Integrable (J u) P)
    (hJmart : ∀ u v : ℝ≥0, u ≤ v →
      ∀ᵐ ω ∂P, condExp (𝓕.rightCont u) P (J v) ω = J u ω)
    (a b : ι → ℝ≥0) (WG WJ : ι → Ω → ℝ)
    (hab : ∀ i ∈ S, a i ≤ b i)
    (hWG : ∀ i ∈ S, Measurable[𝓕.rightCont (a i)] (WG i))
    (hWJ : ∀ i ∈ S, Measurable[𝓕.rightCont (a i)] (WJ i))
    (KG KJ : ℝ)
    (hWGbound : ∀ i ∈ S, ∀ ω, ‖WG i ω‖ ≤ KG)
    (hWJbound : ∀ i ∈ S, ∀ ω, ‖WJ i ω‖ ≤ KJ) :
    Integrable
      (fun ω =>
        (∑ i ∈ S, WG i ω * (R (b i) ω - R (a i) ω)) +
        (∑ i ∈ S, WJ i ω * (J (b i) ω - J (a i) ω))) P ∧
    (∫ ω,
      (∑ i ∈ S, WG i ω * (R (b i) ω - R (a i) ω)) +
      (∑ i ∈ S, WJ i ω * (J (b i) ω - J (a i) ω)) ∂P) = 0 := by
  obtain ⟨hGI, hGzero⟩ :=
    avram_jb20_original_gaussian_finite_mesh_predictable_gain_centered
      S R hRint hRmart a b WG hab hWG KG hWGbound
  obtain ⟨hJI, hJzero⟩ :=
    avram_jb20_original_gaussian_finite_mesh_predictable_gain_centered
      S J hJint hJmart a b WJ hab hWJ KJ hWJbound
  refine ⟨hGI.add hJI, ?_⟩
  rw [integral_add hGI hJI, hGzero, hJzero]
  exact zero_add 0
