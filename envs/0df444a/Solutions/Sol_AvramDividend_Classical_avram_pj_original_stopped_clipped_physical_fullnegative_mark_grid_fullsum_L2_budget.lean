-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_original_stopped_clipped_physical_fullnegative_mark_grid_fullsum_L2_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T12:17:51.246537+00:00
-- url     : https://prove2.me/submissions/25e1f2f0-ccde-4464-86aa-beaff330ac09

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_fullnegative_cutoff_adapted_physical_grid_exact_fullsum_L2
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_fullmark_clipped_physical_grid_L2_uniform_energy
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
    (∀ j ∈ Finset.range m,
      Integrable (fun ω => (N j ω).toReal - r j) P) →
    (∀ i ∈ Finset.range m, ∀ j ∈ Finset.range m,
      Integrable (fun ω => Z i ω * Z j ω) P) →
    (∀ i ∈ Finset.range m, ∀ j ∈ Finset.range m, i < j →
      StronglyMeasurable[𝓕.rightCont (grid j)]
        (fun ω => Z i ω * (if (ρ ω : WithTop ℝ≥0) ≤
          (grid j : WithTop ℝ≥0) then (0 : ℝ) else H j ω))) →
    (∫ ω, (∑ i ∈ Finset.range m, Z i ω)^2 ∂P) ≤
      K^2 * ((n : ℝ) *
        (X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal) := by
  intro Δ grid N r H Z hHI hVInt hPair hPast
  have hStep (j : ℕ) : grid (j + 1) = grid j + Δ := by
    simp only [grid, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
  have hRate (j : ℕ) : r j =
      ((Δ : ℝ≥0∞) *
        X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal := by
    dsimp only [r]
    rw [hStep j, add_tsub_cancel_left]
  have hFull :=
    avram_pj_original_fullnegative_cutoff_adapted_physical_grid_exact_fullsum_L2
      X m cut Δ grid hStep N (by intro j; rfl) r hRate
      (fun i ω => if (ρ ω : WithTop ℝ≥0) ≤
        (grid i : WithTop ℝ≥0) then 0 else H i ω)
      Z (by intro i ω; rfl) hVInt hPair hPast
  have hDiag :=
    avram_pj_workerC_original_fullmark_clipped_physical_grid_L2_uniform_energy
      X x D hD w q K hK cut ρ hρstop n m hn hHI
  have hSum : (∑ i ∈ Finset.range m, ∫ ω, (Z i ω)^2 ∂P) ≤
      K^2 * ((n : ℝ) *
        (X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal) := by
    rw [← integral_finset_sum]
    · exact hDiag
    · intro i hi
      simpa [pow_two] using hPair i hi i hi
  exact hFull.le.trans hSum
