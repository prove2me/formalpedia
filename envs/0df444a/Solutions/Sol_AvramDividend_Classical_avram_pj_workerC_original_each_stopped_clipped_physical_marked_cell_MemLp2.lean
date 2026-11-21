-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_original_each_stopped_clipped_physical_marked_cell_MemLp2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T10:11:28.970186+00:00
-- url     : https://prove2.me/submissions/d36759f3-f12b-4c5a-a7e2-5df3dd5d087c

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_i_original_stopped_discounted_clipped_prejump_gradient_full_cutoff_L2_zero
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
    ∀ i : ℕ, MemLp (Z i) 2 P := by
  intro Δ grid N r H Z i
  let g : ℕ → ℝ≥0 := fun j => grid (i + j)
  have hg (j : ℕ) : g j ≤ g (j + 1) := by
    dsimp [g, grid]
    have hh : i + j ≤ i + (j + 1) := by omega
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hh)
      (by positivity)
  obtain ⟨hL2, _⟩ :=
    avram_p4_s3_interval_i_original_stopped_discounted_clipped_prejump_gradient_full_cutoff_L2_zero
      X x D hD w q K hK cut ρ hρstop g hg 1
  simpa [Finset.sum_range_one, g, grid, N, r, H, Z]
    using hL2
