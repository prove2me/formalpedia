-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_original_physical_quadratic_Hessian_L2_second_moment_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T08:03:54.262786+00:00
-- url     : https://prove2.me/submissions/de5aaf2c-751e-4bfa-b494-62db3c7d11eb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_original_physical_quadratic_Hessian_sum_L2_from_filtered_MDS
import Theorems.Thm_AvramDividend_Classical_avram_ga_original_quadratic_grid_second_moment_rate_tends_zero
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hν : X.ν = 0) (n : ℕ) (hn : 0 < n)
    (H U : ℕ → ℕ → Ω → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hH : ∀ m i ω, |H m i ω| ≤ K)
    (hHI : ∀ (m i : ℕ), i < m + 1 →
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      Integrable (fun ω => (H m i ω * ((X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c) ^ 2 - (Δ : ℝ) * X.σ ^ 2)) ^ 2) P)
    (hUeq : ∀ (m i : ℕ) (ω : Ω),
      U m i ω =
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        H m i ω * ((X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c) ^ 2 - (Δ : ℝ) * X.σ ^ 2))
    (hULp : ∀ m i, MemLp (U m i) 2 P)
    (hUadapt : ∀ (m i : ℕ),
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      StronglyMeasurable[𝓕.rightCont (((i + 1 : ℕ) : ℝ≥0) * Δ)] (U m i))
    (hUcenter : ∀ (m i : ℕ),
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      P[U m i | 𝓕.rightCont ((i : ℝ≥0) * Δ)] =ᵐ[P]
        (fun _ => (0 : ℝ))) :
    Tendsto
      (fun m : ℕ => ∫ ω,
        (∑ i ∈ Finset.range (m + 1), U m i ω) ^ 2 ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨J, _, hRate⟩ :=
    avram_ga_original_physical_quadratic_Hessian_sum_L2_from_filtered_MDS
      X hX hν n hn H U K hK hH hHI hUeq hULp hUadapt hUcenter
  exact avram_ga_original_quadratic_grid_second_moment_rate_tends_zero
    P (fun m ω => ∑ i ∈ Finset.range (m + 1), U m i ω) J hRate
