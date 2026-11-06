-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_original_physical_two_bounded_grid_sums_L2_centered_difference
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:28:49.202307+00:00
-- url     : https://prove2.me/submissions/62b9ca23-313e-4852-b6c1-0b190ec40df1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_predictable_negative_grid_sum_mean_zero_auto
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_physical_bounded_predictable_grid_L2_mean_zero_auto

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Two original bounded predictable finite-grid compensated sums have centred L² differences. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (cut : ℕ)
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (hTime : ∀ i, grid i ≤ T)
    (ε : ℝ) (hε : 0 < ε) (C : ℕ → Set ℝ)
    (hC : ∀ i, MeasurableSet (C i))
    (hBand : ∀ i, C i ⊆ Ioo (-1 : ℝ) (-ε))
    (hCut : ∀ i, C i ⊆ Iic (-(1 / ((cut : ℝ) + 1))))
    (N : ℕ → Ω → ℝ≥0∞)
    (hActual : ∀ i, N i = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ C i))
    (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[𝓕 (grid i)] (H i))
    (hHL2 : ∀ i, MemLp (H i) 2 P)
    (L : ℝ) (hL : ∀ i ω, |H i ω| ≤ L)
    (m n : ℕ) :
    let S : ℕ → Ω → ℝ := fun k ω =>
      ∑ i ∈ Finset.range k, H i ω *
        ((N i ω).toReal -
          (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
            X.ν (C i)).toReal)
    MemLp (fun ω => S n ω - S m ω) 2 P ∧
    (∫ ω, S n ω - S m ω ∂P) = 0 := by
  let S : ℕ → Ω → ℝ := fun k ω =>
    ∑ i ∈ Finset.range k, H i ω *
        ((N i ω).toReal -
          (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
            X.ν (C i)).toReal)
  change MemLp (fun ω => S n ω - S m ω) 2 P ∧
    (∫ ω, S n ω - S m ω ∂P) = 0
  have hL2 (k : ℕ) : MemLp (S k) 2 P :=
    (avram_p4_s3_original_physical_bounded_predictable_grid_L2_mean_zero_auto
      X T cut grid hGrid hTime ε hε C hC hBand hCut
        N hActual H hH hHL2 L hL k).1
  have hOld (k : ℕ) : Integrable (S k) P ∧
      (∫ ω, S k ω ∂P) = 0 :=
    avram_p4_s3_original_predictable_negative_grid_sum_mean_zero_auto
      X T cut grid hGrid hTime ε hε C hC hBand hCut
        N hActual H hH hHL2 k
  constructor
  · exact (hL2 n).sub (hL2 m)
  · rw [integral_sub (hOld n).1 (hOld m).1, (hOld n).2, (hOld m).2]
    exact sub_self 0
