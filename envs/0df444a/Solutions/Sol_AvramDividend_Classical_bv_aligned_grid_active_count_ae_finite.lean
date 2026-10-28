-- Prove2me | solution 1 for AvramDividend.Classical.bv_aligned_grid_active_count_ae_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T13:50:58.843296+00:00
-- url     : https://prove2.me/submissions/3b2fd9e5-1eba-41ad-9990-43d7526f176e

import Theorems.Thm_AvramDividend_Classical_bv_aligned_dyadic_grid_active_count_monotone
import Theorems.Thm_AvramDividend_Classical_bv_monotone_nat_count_uniformly_bounded_ae
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Finset
open scoped NNReal ENNReal

/-- Finite expected counts on all aligned grids yield a finite active-cell ceiling for almost every path. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (Y : Ω → ℝ≥0 → ℝ)
    (grid : ℕ → ℕ → ℝ≥0) (C : ℝ≥0∞)
    (hGrid : ∀ n i : ℕ, grid (n + 1) (2 * i) = grid n i)
    (hY : ∀ t : ℝ≥0, Measurable (fun ω => Y ω t))
    (hBound : ∀ n : ℕ,
      (∫⁻ ω, (∑ i ∈ range (2 ^ n),
        ite (Y ω (grid n i) < Y ω (grid n (i + 1)))
          (1 : ℕ) 0 : ℕ) ∂P) ≤ C)
    (hFinite : C < ⊤) :
    ∀ᵐ ω ∂P, ∃ K : ℕ, ∀ n : ℕ,
      (∑ i ∈ range (2 ^ n),
        ite (Y ω (grid n i) < Y ω (grid n (i + 1)))
          (1 : ℕ) 0) ≤ K := by
  classical
  let F : ℕ → Ω → ℕ := fun n ω =>
    ∑ i ∈ range (2 ^ n),
      ite (Y ω (grid n i) < Y ω (grid n (i + 1))) (1 : ℕ) 0
  have hFN (n : ℕ) : Measurable (F n) := by
    dsimp [F]
    apply Finset.measurable_sum
    intro i hi
    exact Measurable.ite (measurableSet_lt (hY (grid n i))
      (hY (grid n (i + 1)))) measurable_const measurable_const
  have hFM (n : ℕ) : Measurable (fun ω => (F n ω : ℝ≥0∞)) :=
    (measurable_of_countable (fun k : ℕ => (k : ℝ≥0∞))).comp (hFN n)
  have hMono : Monotone (fun n => fun ω => (F n ω : ℝ≥0∞)) := by
    intro n m hnm ω
    have hh : F n ω ≤ F m ω :=
      (bv_aligned_dyadic_grid_active_count_monotone
        (Y ω) grid hGrid) hnm
    change (F n ω : ℝ≥0∞) ≤ (F m ω : ℝ≥0∞)
    exact_mod_cast hh
  exact bv_monotone_nat_count_uniformly_bounded_ae P F C hFM hMono
    hBound hFinite
