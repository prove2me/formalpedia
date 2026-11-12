-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB76_original_two_uniform_grid_generic_predictable_covariance
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T17:40:39.777199+00:00
-- url     : https://prove2.me/submissions/9a7212fa-4b1e-49a1-acc2-c0aa6e4453c0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB83_original_two_mesh_common_refinement_bilinear
import Theorems.Thm_AvramDividend_Classical_avram_gbB78_two_grid_step_cross_time_integral
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (n : ℕ) (hn : 0 < n)
    (G : ℕ → ℕ → Ω → ℝ)
    (hAdapt : ∀ (m i : ℕ),
      Measurable[𝓕.rightCont
        ((i : ℝ≥0) * ((n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)))]
        (G m i))
    (hBound : ∃ B : ℝ, 0 ≤ B ∧ ∀ m i ω, |G m i ω| ≤ B) :
    let L : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
      (Finset.range (m + 1)).sum (fun i =>
        G m i ω * (X.X (s i + Δ) ω - X.X (s i) ω -
          (Δ : ℝ) * X.c))
    let K : ℕ → ℝ → Ω → ℝ := fun m t ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
      (Finset.range (m + 1)).sum (fun i =>
        if (s i : ℝ) ≤ t ∧ t < ((s i + Δ : ℝ≥0) : ℝ)
        then G m i ω else 0)
    ∀ m l,
      (∫ ω, (L m ω) * (L l ω) ∂P) =
        X.σ ^ 2 *
          (∫ t in Ioo (0 : ℝ) (n : ℝ),
            (∫ ω, (K m t ω) * (K l t ω) ∂P) ∂volume) := by
  intro L K m l
  letI : IsProbabilityMeasure P := X.isProbability
  have hStrong : ∀ a i, StronglyMeasurable (G a i) := by
    intro a i
    exact ((hAdapt a i).mono (𝓕.rightCont.le _) le_rfl).stronglyMeasurable
  have hRef := avram_gbB83_original_two_mesh_common_refinement_bilinear
    X hν n hn G hAdapt hBound m l
  have hTime := avram_gbB78_two_grid_step_cross_time_integral
    P n m l hn G hStrong hBound
  dsimp only at hTime
  dsimp only at hRef
  have hTime' :
      (∫ t in Ioo (0 : ℝ) (n : ℝ),
        (∫ ω, (K m t ω) * (K l t ω) ∂P) ∂volume) =
      ((n : ℝ) / (((m + 1) * (l + 1) : ℕ) : ℝ)) *
        (Finset.range ((m + 1) * (l + 1))).sum (fun r =>
          ∫ ω, G m (r / (l + 1)) ω *
            G l (r / (m + 1)) ω ∂P) := by
    simpa only [K] using hTime
  calc
    (∫ ω, (L m ω) * (L l ω) ∂P) =
      (X.σ ^ 2) * ((n : ℝ) / (((m + 1) * (l + 1) : ℕ) : ℝ)) *
        (Finset.range ((m + 1) * (l + 1))).sum (fun r =>
          ∫ ω, G m (r / (l + 1)) ω *
            G l (r / (m + 1)) ω ∂P) := by
              simpa only [L] using hRef
    _ = X.σ ^ 2 *
        (∫ t in Ioo (0 : ℝ) (n : ℝ),
          (∫ ω, (K m t ω) * (K l t ω) ∂P) ∂volume) := by
              rw [hTime']
              ring
