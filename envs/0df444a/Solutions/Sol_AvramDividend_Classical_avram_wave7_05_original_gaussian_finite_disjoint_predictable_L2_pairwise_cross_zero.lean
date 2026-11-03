-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_original_gaussian_finite_disjoint_predictable_L2_pairwise_cross_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T14:35:53.400876+00:00
-- url     : https://prove2.me/submissions/b98ec660-139d-4c43-9216-0235c6ce1f27

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_gaussian_disjoint_predictable_cross_expectation_zero

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
    {ι : Type*} (S : Finset ι)
    (s t : ι → ℝ≥0) (G : ι → Ω → ℝ)
    (hst : ∀ i ∈ S, s i ≤ t i)
    (hSep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → t i ≤ s j ∨ t j ≤ s i)
    (hGown : ∀ i ∈ S, Measurable[𝓕.rightCont (s i)] (G i))
    (hGpair : ∀ i ∈ S, ∀ j ∈ S, t i ≤ s j →
      Measurable[𝓕.rightCont (s j)] (G i))
    (hLp : ∀ i ∈ S, MemLp (fun ω =>
      G i ω * (X.X (t i) ω - X.X (s i) ω -
        ((t i - s i) : ℝ) * X.c)) 2 P) :
    let F : ι → Ω → ℝ := fun i ω =>
      G i ω * (X.X (t i) ω - X.X (s i) ω -
        ((t i - s i) : ℝ) * X.c)
    ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      Integrable (F i * F j) P ∧
        (∫ ω, F i ω * F j ω ∂P) = 0 := by
  classical
  let F : ι → Ω → ℝ := fun i ω =>
    G i ω * (X.X (t i) ω - X.X (s i) ω -
      ((t i - s i) : ℝ) * X.c)
  change ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
    Integrable (F i * F j) P ∧
      (∫ ω, F i ω * F j ω ∂P) = 0
  intro i hi j hj hijNe
  rcases hSep i hi j hj hijNe with hij | hji
  · have h :=
      avram_wave7_05_original_gaussian_disjoint_predictable_cross_expectation_zero
        X hν (s i) (t i) (s j) (t j)
        (hst i hi) hij (hst j hj) (G i) (G j)
        (hGpair i hi j hj hij) (hGown j hj)
        (hLp i hi) (hLp j hj)
    dsimp only at h
    exact h
  · have h :=
      avram_wave7_05_original_gaussian_disjoint_predictable_cross_expectation_zero
        X hν (s j) (t j) (s i) (t i)
        (hst j hj) hji (hst i hi) (G j) (G i)
        (hGpair j hj i hi hji) (hGown i hi)
        (hLp j hj) (hLp i hi)
    dsimp only at h
    have hFI : Integrable (F j * F i) P := h.1
    have hComm : (F i * F j) = (F j * F i) := mul_comm _ _
    have hInt : Integrable (F i * F j) P := by
      rw [hComm]
      exact hFI
    have hEq : (fun ω => F i ω * F j ω) =
        (fun ω => F j ω * F i ω) := by
      funext ω
      ring
    refine ⟨hInt, ?_⟩
    calc
      (∫ ω, F i ω * F j ω ∂P) =
          ∫ ω, F j ω * F i ω ∂P := by rw [hEq]
      _ = 0 := h.2
