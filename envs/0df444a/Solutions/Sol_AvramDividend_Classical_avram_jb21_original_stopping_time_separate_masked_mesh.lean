-- Prove2me | solution 1 for AvramDividend.Classical.avram_jb21_original_stopping_time_separate_masked_mesh
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T20:02:44.506211+00:00
-- url     : https://prove2.me/submissions/c8348283-405a-4b7c-a34b-aab1f4e814cf

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_avram_jb21_original_separate_two_noise_mesh_integrable_centered
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
    (hWJbound : ∀ i ∈ S, ∀ ω, ‖WJ i ω‖ ≤ KJ)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    Integrable (fun ω => ∑ i ∈ S, (if τ ω ≤ a i then 0 else WG i ω) * (R (b i) ω - R (a i) ω)) P ∧
    Integrable (fun ω => ∑ i ∈ S, (if τ ω ≤ a i then 0 else WJ i ω) * (J (b i) ω - J (a i) ω)) P ∧
    (∫ ω, ∑ i ∈ S, (if τ ω ≤ a i then 0 else WG i ω) * (R (b i) ω - R (a i) ω) ∂P) = 0 ∧
    (∫ ω, ∑ i ∈ S, (if τ ω ≤ a i then 0 else WJ i ω) * (J (b i) ω - J (a i) ω) ∂P) = 0 := by
  classical
  let WGm : ι → Ω → ℝ := fun i ω =>
    if τ ω ≤ a i then 0 else WG i ω
  let WJm : ι → Ω → ℝ := fun i ω =>
    if τ ω ≤ a i then 0 else WJ i ω
  have hPast (i : ι) (hi : i ∈ S) :
      MeasurableSet[𝓕.rightCont (a i)] {ω | τ ω ≤ a i} := by
    simpa only [WithTop.coe_le_coe] using hτstop (a i)
  have hmG : ∀ i ∈ S,
      Measurable[𝓕.rightCont (a i)] (WGm i) := by
    intro i hi
    change Measurable[𝓕.rightCont (a i)]
      (fun ω => if τ ω ≤ a i then 0 else WG i ω)
    exact Measurable.ite (hPast i hi) measurable_const (hWG i hi)
  have hmJ : ∀ i ∈ S,
      Measurable[𝓕.rightCont (a i)] (WJm i) := by
    intro i hi
    change Measurable[𝓕.rightCont (a i)]
      (fun ω => if τ ω ≤ a i then 0 else WJ i ω)
    exact Measurable.ite (hPast i hi) measurable_const (hWJ i hi)
  have hbG : ∀ i ∈ S, ∀ ω, ‖WGm i ω‖ ≤ KG := by
    intro i hi ω
    change ‖if τ ω ≤ a i then 0 else WG i ω‖ ≤ KG
    split_ifs with h
    · simpa only [norm_zero] using
        ((norm_nonneg (WG i ω)).trans (hWGbound i hi ω))
    · exact hWGbound i hi ω
  have hbJ : ∀ i ∈ S, ∀ ω, ‖WJm i ω‖ ≤ KJ := by
    intro i hi ω
    change ‖if τ ω ≤ a i then 0 else WJ i ω‖ ≤ KJ
    split_ifs with h
    · simpa only [norm_zero] using
        ((norm_nonneg (WJ i ω)).trans (hWJbound i hi ω))
    · exact hWJbound i hi ω
  have hCert :=
    avram_jb21_original_separate_two_noise_mesh_integrable_centered
      S R J hRint hRmart hJint hJmart
      a b WGm WJm hab hmG hmJ KG KJ hbG hbJ
  simpa only [WGm, WJm] using hCert
