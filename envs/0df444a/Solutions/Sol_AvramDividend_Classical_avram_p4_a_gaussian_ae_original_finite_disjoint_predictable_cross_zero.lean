-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_ae_original_finite_disjoint_predictable_cross_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:52:11.940293+00:00
-- url     : https://prove2.me/submissions/61cb05a6-9e0d-4597-ac64-e677b8a562f4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_gaussian_finite_disjoint_predictable_L2_pairwise_cross_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Pairwise orthogonality of original jump-subtracted Gaussian residual
cells on a finite, disjoint deterministic predictable grid. The single
all-times Levy-Ito path equality is explicitly assumed only almost surely. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      X.X u ω = (u : ℝ) * X.c +
        (Y.X u ω - (u : ℝ) * Y.c) + Jsmall u ω + Jlarge u ω)
    {ι : Type*} (S : Finset ι)
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
    ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      Integrable (F i * F j) P ∧ (∫ ω, F i ω * F j ω ∂P) = 0 := by
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
  have hCross :=
    avram_wave7_05_original_gaussian_finite_disjoint_predictable_L2_pairwise_cross_zero
      Y hYν S s t G hst hSep hGown hGpair hLpY
  change ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
    Integrable (F i * F j) P ∧ (∫ ω, F i ω * F j ω ∂P) = 0
  intro i hi j hj hne
  obtain ⟨hIntY, hZeroY⟩ := hCross i hi j hj hne
  have hProd : (fun ω => F i ω * F j ω) =ᵐ[P]
      (fun ω => FY i ω * FY j ω) := by
    filter_upwards [hAE i hi, hAE j hj] with ω hiω hjω
    change F i ω * F j ω = FY i ω * FY j ω
    rw [hiω, hjω]
  refine ⟨hIntY.congr hProd.symm, ?_⟩
  rw [integral_congr_ae hProd, hZeroY]
