-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_original_gaussian_finite_predictable_offdiagonal_row_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T14:57:05.923203+00:00
-- url     : https://prove2.me/submissions/7647675b-14bf-4229-9b56-8550c02f690e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_gaussian_finite_disjoint_predictable_L2_pairwise_cross_zero

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
    {ι : Type*} [DecidableEq ι] (S : Finset ι)
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
    ∀ i ∈ S,
      Integrable (fun ω => ∑ j ∈ S.erase i, F i ω * F j ω) P ∧
      (∫ ω, ∑ j ∈ S.erase i, F i ω * F j ω ∂P) = 0 := by
  classical
  let F : ι → Ω → ℝ := fun i ω =>
    G i ω * (X.X (t i) ω - X.X (s i) ω -
      ((t i - s i) : ℝ) * X.c)
  change ∀ i ∈ S,
    Integrable (fun ω => ∑ j ∈ S.erase i, F i ω * F j ω) P ∧
    (∫ ω, ∑ j ∈ S.erase i, F i ω * F j ω ∂P) = 0
  have hPair :=
    avram_wave7_05_original_gaussian_finite_disjoint_predictable_L2_pairwise_cross_zero
      X hν S s t G hst hSep hGown hGpair hLp
  dsimp only at hPair
  intro i hi
  have hOne : ∀ j ∈ S.erase i,
      Integrable (fun ω => F i ω * F j ω) P ∧
        (∫ ω, F i ω * F j ω ∂P) = 0 := by
    intro j hj
    obtain ⟨hji, hjS⟩ := Finset.mem_erase.mp hj
    have h := hPair i hi j hjS (Ne.symm hji)
    have hfi : (F i * F j) = (fun ω => F i ω * F j ω) := by
      funext ω
      simp only [Pi.mul_apply]
    have hInt : Integrable (fun ω => F i ω * F j ω) P := by
      rw [←hfi]
      exact h.1
    refine ⟨hInt, ?_⟩
    exact h.2
  have hInt : ∀ j ∈ S.erase i,
      Integrable (fun ω => F i ω * F j ω) P := by
    intro j hj
    exact (hOne j hj).1
  constructor
  · exact integrable_finset_sum (S.erase i) hInt
  · rw [integral_finset_sum (S.erase i) hInt]
    exact Finset.sum_eq_zero (by
      intro j hj
      exact (hOne j hj).2)
