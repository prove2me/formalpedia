-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gaussian14_original_deterministic_grid_two_weights_L2_isometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T15:00:32.199391+00:00
-- url     : https://prove2.me/submissions/61f8883c-61b8-4325-b28a-f6164a769a9d

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_gaussian_finite_predictable_grid_exact_L2_isometry

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The exact same-source Gaussian isometry controls the difference of two
original predictable integrands on a common disjoint deterministic grid. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (s t : ι → ℝ≥0) (G H : ι → Ω → ℝ)
    (hst : ∀ i ∈ S, s i ≤ t i)
    (hSep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → t i ≤ s j ∨ t j ≤ s i)
    (hGown : ∀ i ∈ S, Measurable[𝓕.rightCont (s i)] (G i))
    (hHown : ∀ i ∈ S, Measurable[𝓕.rightCont (s i)] (H i))
    (hGpair : ∀ i ∈ S, ∀ j ∈ S, t i ≤ s j →
      Measurable[𝓕.rightCont (s j)] (G i))
    (hHpair : ∀ i ∈ S, ∀ j ∈ S, t i ≤ s j →
      Measurable[𝓕.rightCont (s j)] (H i))
    (hLp : ∀ i ∈ S, MemLp (fun ω =>
      (G i ω - H i ω) * (X.X (t i) ω - X.X (s i) ω -
        ((t i - s i) : ℝ) * X.c)) 2 P) :
    let d : ι → Ω → ℝ := fun i ω =>
      X.X (t i) ω - X.X (s i) ω - ((t i - s i) : ℝ) * X.c
    let QG : Ω → ℝ := fun ω => ∑ i ∈ S, G i ω * d i ω
    let QH : Ω → ℝ := fun ω => ∑ i ∈ S, H i ω * d i ω
    MemLp (QG - QH) 2 P ∧
      Integrable (fun ω => (QG ω - QH ω) ^ 2) P ∧
      (∫ ω, (QG ω - QH ω) ^ 2 ∂P) =
        ∑ i ∈ S, (∫ ω, ((G i ω - H i ω) * d i ω) ^ 2 ∂P) := by
  let d : ι → Ω → ℝ := fun i ω =>
    X.X (t i) ω - X.X (s i) ω - ((t i - s i) : ℝ) * X.c
  let QG : Ω → ℝ := fun ω => ∑ i ∈ S, G i ω * d i ω
  let QH : Ω → ℝ := fun ω => ∑ i ∈ S, H i ω * d i ω
  have hown : ∀ i ∈ S, Measurable[𝓕.rightCont (s i)]
      (fun ω => G i ω - H i ω) := by
    intro i hi
    exact (hGown i hi).sub (hHown i hi)
  have hpair : ∀ i ∈ S, ∀ j ∈ S, t i ≤ s j →
      Measurable[𝓕.rightCont (s j)] (fun ω => G i ω - H i ω) := by
    intro i hi j hj hij
    exact (hGpair i hi j hj hij).sub (hHpair i hi j hj hij)
  have hisom :=
    avram_wave7_05_original_gaussian_finite_predictable_grid_exact_L2_isometry
      X hν S s t (fun i ω => G i ω - H i ω) hst hSep hown hpair hLp
  have hsum (ω : Ω) :
      (∑ i ∈ S, (G i ω - H i ω) * d i ω) = QG ω - QH ω := by
    dsimp [QG, QH]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hfun :
      (fun ω => ∑ i ∈ S, (G i ω - H i ω) * d i ω) =
        (fun ω => QG ω - QH ω) := by
    funext ω
    exact hsum ω
  have hsquare :
      (fun ω => (∑ i ∈ S, (G i ω - H i ω) * d i ω) ^ 2) =
        (fun ω => (QG ω - QH ω) ^ 2) := by
    funext ω
    rw [hsum]
  obtain ⟨hmem, hint, heq⟩ := hisom
  change MemLp (fun ω => ∑ i ∈ S, (G i ω - H i ω) * d i ω) 2 P at hmem
  change Integrable
    (fun ω => (∑ i ∈ S, (G i ω - H i ω) * d i ω) ^ 2) P at hint
  change (∫ ω, (∑ i ∈ S, (G i ω - H i ω) * d i ω) ^ 2 ∂P) =
    ∑ i ∈ S, (∫ ω, ((G i ω - H i ω) * d i ω) ^ 2 ∂P) at heq
  rw [hfun] at hmem
  rw [hsquare] at hint heq
  exact ⟨hmem, hint, heq⟩
