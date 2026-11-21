-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_original_fullnegative_cutoff_adapted_physical_grid_exact_fullsum_L2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T10:26:52.350334+00:00
-- url     : https://prove2.me/submissions/95d2486e-e4c7-403a-a32d-aa896c43a144

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_rightcont_conditional_L2_exact
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_predictable_conditionally_centered_physical_grid_L2_isometry
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original spectrally negative Lévy full negative-cutoff physical marked
grid has exact full-sum L2 energy under true past-adapted weights. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (m cut : ℕ) (Δ : ℝ≥0) (grid : ℕ → ℝ≥0)
    (hStep : ∀ j, grid (j + 1) = grid j + Δ)
    (N : ℕ → Ω → ℝ≥0∞)
    (hActual : ∀ j, N j = fun ω =>
      ((Measure.count.restrict {t : ℝ≥0 |
        0 < t ∧ X.X t ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t,
          X.X t ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) t)))
        (Ioc (grid j) (grid (j + 1)) ×ˢ
          Iic (-(1 / ((cut : ℝ) + 1)))))
    (r : ℕ → ℝ)
    (hRate : ∀ j, r j =
      ((Δ : ℝ≥0∞) *
        X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal)
    (H Z : ℕ → Ω → ℝ)
    (hZ : ∀ i ω, Z i ω = H i ω * ((N i ω).toReal - r i))
    (hVInt : ∀ j ∈ Finset.range m,
      Integrable (fun ω => (N j ω).toReal - r j) P)
    (hPair : ∀ i ∈ Finset.range m, ∀ j ∈ Finset.range m,
      Integrable (fun ω => Z i ω * Z j ω) P)
    (hPast : ∀ i ∈ Finset.range m, ∀ j ∈ Finset.range m,
      i < j →
      StronglyMeasurable[𝓕.rightCont (grid j)]
        (fun ω => Z i ω * H j ω)) :
    (∫ ω, (∑ i ∈ Finset.range m, Z i ω)^2 ∂P) =
      ∑ i ∈ Finset.range m, ∫ ω, (Z i ω)^2 ∂P := by
  have hCond (j : ℕ) (hj : j ∈ Finset.range m) :
      P[(fun ω => (N j ω).toReal - r j) |
        𝓕.rightCont (grid j)] =ᵐ[P] (fun _ => 0) := by
    have hOrig :=
      (avram_p4_s3_interval_h_original_full_cutoff_rightcont_conditional_L2_exact
        X (grid j) Δ cut).1
    rw [hActual j, hRate j, hStep j]
    exact hOrig
  exact avram_pj_original_predictable_conditionally_centered_physical_grid_L2_isometry
    P m (fun j => 𝓕.rightCont (grid j))
    (fun j => 𝓕.rightCont.le (grid j))
    H (fun j ω => (N j ω).toReal - r j) Z
    hZ hVInt hCond hPair hPast
