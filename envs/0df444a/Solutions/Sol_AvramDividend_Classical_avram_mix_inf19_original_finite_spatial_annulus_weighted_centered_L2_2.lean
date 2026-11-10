-- Prove2me | solution 2 for AvramDividend.Classical.avram_mix_inf19_original_finite_spatial_annulus_weighted_centered_L2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T18:38:17.354082+00:00
-- url     : https://prove2.me/submissions/600575ca-49a2-45b1-98d9-3081fe7ef3e0

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_annulus15_original_bounded_predictable_annulus_grid_L2_zero_mean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

/-- Finite real combinations of original compensated negative-annulus counts are L² and centred. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (cut : ℕ → ℕ) (hcut : Monotone cut) (a : ℕ → ℝ) :
    let B : ℕ → Set ℝ := fun i =>
      Ioc (-(1 / ((cut i : ℝ) + 1))) (-(1 / ((cut (i + 1) : ℝ) + 1)))
    let N : ℕ → Ω → ℝ≥0∞ := fun i ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B i)
    let r : ℕ → ℝ := fun i => ((T : ℝ≥0∞) * X.ν (B i)).toReal
    let Y : ℕ → Ω → ℝ := fun i ω => (N i ω).toReal - r i
    ∀ k : ℕ,
      MemLp (fun ω => ∑ i ∈ Finset.range k, a i * Y i ω) 2 P ∧
      (∫ ω, ∑ i ∈ Finset.range k, a i * Y i ω ∂P) = 0 := by
  classical
  let B : ℕ → Set ℝ := fun i =>
    Ioc (-(1 / ((cut i : ℝ) + 1))) (-(1 / ((cut (i + 1) : ℝ) + 1)))
  let N : ℕ → Ω → ℝ≥0∞ := fun i ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B i)
  let r : ℕ → ℝ := fun i => ((T : ℝ≥0∞) * X.ν (B i)).toReal
  let Y : ℕ → Ω → ℝ := fun i ω => (N i ω).toReal - r i
  change ∀ k, MemLp (fun ω => ∑ i ∈ Finset.range k, a i * Y i ω) 2 P ∧
    (∫ ω, ∑ i ∈ Finset.range k, a i * Y i ω ∂P) = 0
  have hOne : ∀ i, MemLp (fun ω => a i * Y i ω) 2 P ∧
      (∫ ω, a i * Y i ω ∂P) = 0 := by
    intro i
    let grid : ℕ → ℝ≥0 := fun j => if j = 0 then 0 else T
    have hGrid : ∀ j, grid j ≤ grid (j + 1) := by
      intro j
      cases j with
      | zero => simp [grid]
      | succ j => simp [grid]
    have h := avram_mix_annulus15_original_bounded_predictable_annulus_grid_L2_zero_mean
      X (cut i) (cut (i + 1)) (hcut (Nat.le_succ i))
      grid hGrid (fun _ _ => a i)
      (by intro j; exact stronglyMeasurable_const) |a i|
      (by intro j ω; exact le_refl _) 1
    simpa [grid, B, N, r, Y] using h
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hI : Integrable (fun ω => ∑ i ∈ Finset.range k, a i * Y i ω) P :=
      ih.1.integrable (by norm_num)
    have hJ : Integrable (fun ω => a k * Y k ω) P :=
      (hOne k).1.integrable (by norm_num)
    constructor
    · have hSumEq :
          (fun ω => ∑ i ∈ Finset.range (k + 1), a i * Y i ω) =
            (fun ω => (∑ i ∈ Finset.range k, a i * Y i ω) +
              a k * Y k ω) := by
          funext ω
          rw [Finset.sum_range_succ]
      rw [hSumEq]
      exact ih.1.add (hOne k).1
    · calc
        (∫ ω, ∑ i ∈ Finset.range (k + 1), a i * Y i ω ∂P) =
            (∫ ω, ∑ i ∈ Finset.range k, a i * Y i ω ∂P) +
            (∫ ω, a k * Y k ω ∂P) := by
              simp only [Finset.sum_range_succ]
              exact integral_add hI hJ
        _ = 0 := by rw [ih.2, (hOne k).2]; ring
