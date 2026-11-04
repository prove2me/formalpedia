-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_ae_original_finite_grid_exact_L2_isometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:52:55.161021+00:00
-- url     : https://prove2.me/submissions/a3087b4a-f13b-4968-9830-15116c4a070c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_gaussian_finite_predictable_grid_exact_L2_isometry
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Exact L² energy for original X's Gaussian residual on a finite,
predictable, disjoint deterministic grid, from an a.s. all-time extraction. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      X.X u ω = (u : ℝ) * X.c +
        (Y.X u ω - (u : ℝ) * Y.c) + Jsmall u ω + Jlarge u ω)
    {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (s t : ι → ℝ≥0) (G : ι → Ω → ℝ)
    (hst : ∀ i ∈ S, s i ≤ t i)
    (hSep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → t i ≤ s j ∨ t j ≤ s i)
    (hGown : ∀ i ∈ S, Measurable[𝓕.rightCont (s i)] (G i))
    (hGpair : ∀ i ∈ S, ∀ j ∈ S, t i ≤ s j →
      Measurable[𝓕.rightCont (s j)] (G i))
    (hLp : ∀ i ∈ S, MemLp (fun ω => G i ω *
      ((X.X (t i) ω - (t i : ℝ) * X.c - Jsmall (t i) ω - Jlarge (t i) ω) -
       (X.X (s i) ω - (s i : ℝ) * X.c - Jsmall (s i) ω - Jlarge (s i) ω))) 2 P) :
    let F : ι → Ω → ℝ := fun i ω => G i ω *
      ((X.X (t i) ω - (t i : ℝ) * X.c - Jsmall (t i) ω - Jlarge (t i) ω) -
       (X.X (s i) ω - (s i : ℝ) * X.c - Jsmall (s i) ω - Jlarge (s i) ω))
    MemLp (fun ω => ∑ i ∈ S, F i ω) 2 P ∧
    Integrable (fun ω => (∑ i ∈ S, F i ω) ^ 2) P ∧
    (∫ ω, (∑ i ∈ S, F i ω) ^ 2 ∂P) =
      ∑ i ∈ S, (∫ ω, (F i ω) ^ 2 ∂P) := by
  let F : ι → Ω → ℝ := fun i ω => G i ω *
    ((X.X (t i) ω - (t i : ℝ) * X.c - Jsmall (t i) ω - Jlarge (t i) ω) -
     (X.X (s i) ω - (s i : ℝ) * X.c - Jsmall (s i) ω - Jlarge (s i) ω))
  let FY : ι → Ω → ℝ := fun i ω => G i ω *
    (Y.X (t i) ω - Y.X (s i) ω - ((t i - s i) : ℝ) * Y.c)
  have hAE (i : ι) (hi : i ∈ S) : F i =ᵐ[P] FY i := by
    filter_upwards [hSourceDecomp] with ω hω
    dsimp [F, FY]
    rw [hω (t i), hω (s i)]
    ring
  have hLpY : ∀ i ∈ S, MemLp (FY i) 2 P := by
    intro i hi
    exact (memLp_congr_ae (hAE i hi)).1 (hLp i hi)
  obtain ⟨hSrcLp, hSrcInt, hSrcEq⟩ :=
    avram_wave7_05_original_gaussian_finite_predictable_grid_exact_L2_isometry
      Y hYν S s t G hst hSep hGown hGpair hLpY
  have hSumAE : (fun ω => ∑ i ∈ S, F i ω) =ᵐ[P]
      (fun ω => ∑ i ∈ S, FY i ω) := by
    filter_upwards [hSourceDecomp] with ω hω
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [F, FY]
    rw [hω (t i), hω (s i)]
    ring
  have hSqAE : (fun ω => (∑ i ∈ S, F i ω) ^ 2) =ᵐ[P]
      (fun ω => (∑ i ∈ S, FY i ω) ^ 2) := by
    filter_upwards [hSumAE] with ω hω
    rw [hω]
  change MemLp (fun ω => ∑ i ∈ S, F i ω) 2 P ∧
    Integrable (fun ω => (∑ i ∈ S, F i ω) ^ 2) P ∧
    (∫ ω, (∑ i ∈ S, F i ω) ^ 2 ∂P) =
      ∑ i ∈ S, (∫ ω, (F i ω) ^ 2 ∂P)
  refine ⟨(memLp_congr_ae hSumAE).2 hSrcLp,
    hSrcInt.congr hSqAE.symm, ?_⟩
  calc
    (∫ ω, (∑ i ∈ S, F i ω) ^ 2 ∂P) =
        (∫ ω, (∑ i ∈ S, FY i ω) ^ 2 ∂P) := integral_congr_ae hSqAE
    _ = ∑ i ∈ S, (∫ ω, (FY i ω) ^ 2 ∂P) := hSrcEq
    _ = ∑ i ∈ S, (∫ ω, (F i ω) ^ 2 ∂P) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hCellSq : (fun ω => (F i ω) ^ 2) =ᵐ[P]
          (fun ω => (FY i ω) ^ 2) := by
        filter_upwards [hAE i hi] with ω hω
        rw [hω]
      exact (integral_congr_ae hCellSq).symm
