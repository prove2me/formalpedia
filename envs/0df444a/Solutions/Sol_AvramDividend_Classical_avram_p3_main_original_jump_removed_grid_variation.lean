-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_main_original_jump_removed_grid_variation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T08:52:08.940585+00:00
-- url     : https://prove2.me/submissions/a17c19fd-6c55-4498-abed-302b1a644089

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_monotone
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The genuine negative-jump-removed original BV source has finite grid
variation controlled by the physical drift and monotone, possibly nonzero
continuous original residual, on one P-full sample event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t => (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
      else 0)
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
      ∀ (n : ℕ) (u : ℕ → ℝ≥0),
        (∀ i, i < n → u i ≤ u (i + 1)) →
        (∑ i ∈ Finset.range n,
          |Y (u (i + 1)) - Y (u i)|) ≤
          |X.drift| * ((u n : ℝ) - (u 0 : ℝ)) +
            (R (u n) - R (u 0)) := by
  filter_upwards
    [avram_p3_a_bvdrift_original_raw_removed_residual_monotone X hBV]
    with ω hmono
  let J : ℝ≥0 → ℝ := fun t => (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
      else 0)
  let R : ℝ≥0 → ℝ := fun t =>
    ((t : ℝ) * X.drift - X.X t ω) - J t
  let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
  change ∀ (n : ℕ) (u : ℕ → ℝ≥0),
    (∀ i, i < n → u i ≤ u (i + 1)) →
    (∑ i ∈ Finset.range n, |Y (u (i + 1)) - Y (u i)|) ≤
      |X.drift| * ((u n : ℝ) - (u 0 : ℝ)) +
        (R (u n) - R (u 0))
  intro n u hu
  have ht (i : ℕ) (hi : i < n) :
      (u i : ℝ) ≤ (u (i + 1) : ℝ) := by
    exact_mod_cast hu i hi
  have hr (i : ℕ) (hi : i < n) :
      R (u i) ≤ R (u (i + 1)) := by
    simpa only [R, J] using hmono (hu i hi)
  have hvariation :
      (∑ i ∈ Finset.range n,
        |X.drift * ((u (i + 1) : ℝ) - (u i : ℝ)) -
          (R (u (i + 1)) - R (u i))|) ≤
        |X.drift| * ((u n : ℝ) - (u 0 : ℝ)) +
          (R (u n) - R (u 0)) := by
    classical
    have hboundCell (i : ℕ) (hi : i < n) :
        |X.drift * ((u (i + 1) : ℝ) - (u i : ℝ)) -
          (R (u (i + 1)) - R (u i))| ≤
          |X.drift| * ((u (i + 1) : ℝ) - (u i : ℝ)) +
            (R (u (i + 1)) - R (u i)) := by
      have ht0 : 0 ≤ (u (i + 1) : ℝ) - (u i : ℝ) :=
        sub_nonneg.mpr (ht i hi)
      have hr0 : 0 ≤ R (u (i + 1)) - R (u i) :=
        sub_nonneg.mpr (hr i hi)
      calc
        |X.drift * ((u (i + 1) : ℝ) - (u i : ℝ)) -
          (R (u (i + 1)) - R (u i))| =
            |X.drift * ((u (i + 1) : ℝ) - (u i : ℝ)) +
              (-(R (u (i + 1)) - R (u i)))| := by ring
        _ ≤ |X.drift * ((u (i + 1) : ℝ) - (u i : ℝ))| +
            |-(R (u (i + 1)) - R (u i))| := abs_add_le _ _
        _ = |X.drift| * ((u (i + 1) : ℝ) - (u i : ℝ)) +
              (R (u (i + 1)) - R (u i)) := by
          rw [abs_mul, abs_neg, abs_of_nonneg ht0, abs_of_nonneg hr0]
    have htel (f : ℕ → ℝ) (k : ℕ) :
        (∑ i ∈ Finset.range k, (f (i + 1) - f i)) = f k - f 0 := by
      induction k with
      | zero => simp
      | succ k ih =>
        simp only [Finset.sum_range_succ]
        rw [ih]
        ring
    calc
      (∑ i ∈ Finset.range n,
        |X.drift * ((u (i + 1) : ℝ) - (u i : ℝ)) -
          (R (u (i + 1)) - R (u i))|) ≤
          ∑ i ∈ Finset.range n,
            (|X.drift| * ((u (i + 1) : ℝ) - (u i : ℝ)) +
              (R (u (i + 1)) - R (u i))) := by
        apply Finset.sum_le_sum
        intro i hi
        exact hboundCell i (Finset.mem_range.mp hi)
      _ = |X.drift| * ((u n : ℝ) - (u 0 : ℝ)) +
            (R (u n) - R (u 0)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum,
          htel (fun i => (u i : ℝ)) n,
          htel (fun i => R (u i)) n]
  have hcell (i : ℕ) :
      Y (u (i + 1)) - Y (u i) =
        X.drift * ((u (i + 1) : ℝ) - (u i : ℝ)) -
          (R (u (i + 1)) - R (u i)) := by
    dsimp [Y, R, J]
    ring
  calc
    (∑ i ∈ Finset.range n,
      |Y (u (i + 1)) - Y (u i)|) =
        (∑ i ∈ Finset.range n,
          |X.drift * ((u (i + 1) : ℝ) - (u i : ℝ)) -
            (R (u (i + 1)) - R (u i))|) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [hcell i]
    _ ≤ |X.drift| * ((u n : ℝ) - (u 0 : ℝ)) +
        (R (u n) - R (u 0)) := by
          simpa only using hvariation
