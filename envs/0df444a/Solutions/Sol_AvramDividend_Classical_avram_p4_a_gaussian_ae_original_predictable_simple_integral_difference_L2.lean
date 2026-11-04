-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_ae_original_predictable_simple_integral_difference_L2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:34:36.013199+00:00
-- url     : https://prove2.me/submissions/bce7a1de-bee0-47a3-bbe8-314a94cfc0ad

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ae_original_finite_grid_exact_L2_isometry
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- The L² error between two original-X Gaussian predictable simple
integrals is exactly the sum of disjoint cell-error energies. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*} [DecidableEq ι]
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      X.X u ω = (u : ℝ) * X.c +
        (Y.X u ω - (u : ℝ) * Y.c) + Jsmall u ω + Jlarge u ω)
    (S : Finset ι) (s t : ι → ℝ≥0) (G H : ι → Ω → ℝ)
    (hst : ∀ i ∈ S, s i ≤ t i)
    (hSep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      t i ≤ s j ∨ t j ≤ s i)
    (hGown : ∀ i ∈ S, Measurable[𝓕.rightCont (s i)] (G i))
    (hHown : ∀ i ∈ S, Measurable[𝓕.rightCont (s i)] (H i))
    (hGpair : ∀ i ∈ S, ∀ j ∈ S, t i ≤ s j →
      Measurable[𝓕.rightCont (s j)] (G i))
    (hHpair : ∀ i ∈ S, ∀ j ∈ S, t i ≤ s j →
      Measurable[𝓕.rightCont (s j)] (H i))
    (hLp : ∀ i ∈ S, MemLp (fun ω => (G i ω - H i ω) *
      ((X.X (t i) ω - (t i : ℝ) * X.c - Jsmall (t i) ω - Jlarge (t i) ω) -
       (X.X (s i) ω - (s i : ℝ) * X.c - Jsmall (s i) ω - Jlarge (s i) ω))) 2 P) :
    let M : ι → Ω → ℝ := fun i ω =>
      (X.X (t i) ω - (t i : ℝ) * X.c -
        Jsmall (t i) ω - Jlarge (t i) ω) -
      (X.X (s i) ω - (s i : ℝ) * X.c -
        Jsmall (s i) ω - Jlarge (s i) ω)
    let SG : Ω → ℝ := fun ω => ∑ i ∈ S, G i ω * M i ω
    let SH : Ω → ℝ := fun ω => ∑ i ∈ S, H i ω * M i ω
    MemLp (fun ω => SG ω - SH ω) 2 P ∧
    Integrable (fun ω => (SG ω - SH ω) ^ 2) P ∧
    (∫ ω, (SG ω - SH ω) ^ 2 ∂P) =
      ∑ i ∈ S, (∫ ω, ((G i ω - H i ω) * M i ω) ^ 2 ∂P) := by
  let M : ι → Ω → ℝ := fun i ω =>
    (X.X (t i) ω - (t i : ℝ) * X.c -
      Jsmall (t i) ω - Jlarge (t i) ω) -
    (X.X (s i) ω - (s i : ℝ) * X.c -
      Jsmall (s i) ω - Jlarge (s i) ω)
  let SG : Ω → ℝ := fun ω => ∑ i ∈ S, G i ω * M i ω
  let SH : Ω → ℝ := fun ω => ∑ i ∈ S, H i ω * M i ω
  let SR : Ω → ℝ := fun ω => ∑ i ∈ S, (G i ω - H i ω) * M i ω
  have hOwn : ∀ i ∈ S,
      Measurable[𝓕.rightCont (s i)] (fun ω => G i ω - H i ω) := by
    intro i hi
    exact (hGown i hi).sub (hHown i hi)
  have hPair : ∀ i ∈ S, ∀ j ∈ S, t i ≤ s j →
      Measurable[𝓕.rightCont (s j)] (fun ω => G i ω - H i ω) := by
    intro i hi j hj hij
    exact (hGpair i hi j hj hij).sub (hHpair i hi j hj hij)
  obtain ⟨hSourceLp, hSourceInt, hSourceIsom⟩ :=
    avram_p4_a_gaussian_ae_original_finite_grid_exact_L2_isometry
      X Y hYν hYσ Jsmall Jlarge hSourceDecomp
      S s t (fun i ω => G i ω - H i ω) hst hSep hOwn hPair hLp
  have hDiff (ω : Ω) : SG ω - SH ω = SR ω := by
    dsimp [SG, SH, SR]
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
  have hDiffAE : (fun ω => SG ω - SH ω) =ᵐ[P] SR := by
    filter_upwards [] with ω
    exact hDiff ω
  have hSqAE : (fun ω => (SG ω - SH ω) ^ 2) =ᵐ[P]
      (fun ω => SR ω ^ 2) := by
    filter_upwards [hDiffAE] with ω he
    rw [he]
  change MemLp (fun ω => SG ω - SH ω) 2 P ∧
    Integrable (fun ω => (SG ω - SH ω) ^ 2) P ∧
    (∫ ω, (SG ω - SH ω) ^ 2 ∂P) =
      ∑ i ∈ S, (∫ ω, ((G i ω - H i ω) * M i ω) ^ 2 ∂P)
  exact ⟨(memLp_congr_ae hDiffAE).2 hSourceLp,
    hSourceInt.congr hSqAE.symm,
    (integral_congr_ae hSqAE).trans hSourceIsom⟩
