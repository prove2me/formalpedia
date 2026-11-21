-- Prove2me | solution 2 for AvramDividend.Classical.avram_pj_workerC_original_stopped_negative_mark_physical_fullsum_L2_from_orthogonality
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T10:02:03.785913+00:00
-- url     : https://prove2.me/submissions/e66fe2d3-d0e5-43fc-8a80-695bae481aed

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_fullmark_clipped_physical_grid_L2_uniform_energy
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_marked_grid_pairwise_L2_orthogonality_yields_full_sum_energy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q K : ℝ) (hK : 0 ≤ K)
    (cut : ℕ) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (n m : ℕ) (hn : 0 < n) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let grid : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let N : ℕ → Ω → ℝ≥0∞ := fun i ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ Iic (-(1 / ((cut : ℝ) + 1))))
    let r : ℕ → ℝ := fun i =>
      (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
        X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal
    let H : ℕ → Ω → ℝ := fun i ω =>
      max (-K) (min K (Real.exp (-(q * (grid i : ℝ))) *
        deriv w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω)
          (grid i))))
    let Z : ℕ → Ω → ℝ := fun i ω =>
      (if (ρ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
        then (0 : ℝ) else H i ω) * ((N i ω).toReal - r i)
    (∀ i ∈ Finset.range m,
      Integrable (fun ω =>
        (if (ρ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
          then (0 : ℝ) else H i ω)^2) P) →
    (∀ i ∈ Finset.range m, ∀ j ∈ Finset.range m,
      Integrable (fun ω => Z i ω * Z j ω) P) →
    (∀ i ∈ Finset.range m, ∀ j ∈ Finset.range m, i ≠ j →
      (∫ ω, Z i ω * Z j ω ∂P) = 0) →
    (∫ ω, (∑ i ∈ Finset.range m, Z i ω)^2 ∂P) ≤
      K^2 * ((n : ℝ) *
        (X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal) := by
  intro Δ grid N r H Z hHI hPair hCross
  have hDiag :=
    avram_pj_workerC_original_fullmark_clipped_physical_grid_L2_uniform_energy
      X x D hD w q K hK cut ρ hρstop n m hn hHI
  have hOrth :=
    avram_pj_original_marked_grid_pairwise_L2_orthogonality_yields_full_sum_energy
      P (Finset.range m) Z hPair hCross
  have hIntegral :
      (∫ ω, ∑ i ∈ Finset.range m, (Z i ω)^2 ∂P) =
        ∑ i ∈ Finset.range m, ∫ ω, (Z i ω)^2 ∂P := by
    apply integral_finset_sum
    intro i hi
    simpa only [pow_two] using hPair i hi i hi
  rw [hOrth, ← hIntegral]
  exact hDiag
