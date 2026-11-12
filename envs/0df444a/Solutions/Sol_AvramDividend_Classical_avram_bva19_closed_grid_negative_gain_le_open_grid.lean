-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva19_closed_grid_negative_gain_le_open_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T18:02:12.062206+00:00
-- url     : https://prove2.me/submissions/a9101c89-06e3-48bb-9b7a-a063a073bb65

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    (C : ℝ≥0∞) (u : ℕ → ℕ → ℝ≥0)
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1))
    (τ : ℝ≥0∞) (U : ℝ≥0 → ℝ) (q : ℝ)
    (ψ : ℝ → ℝ)
    (hψ : ∀ a : ℝ, 0 ≤ a → ENNReal.ofReal a ≤ C → ψ a ≤ 0)
    (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1),
      if (u n i : ℝ≥0∞) < τ ∧
          0 ≤ U (u n i) ∧ ENNReal.ofReal (U (u n i)) ≤ C then
        Real.exp (-(q * (u n i : ℝ))) * ψ (U (u n i)) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0) ≤
    (∑ i ∈ Finset.range (n + 1),
      if (u n i : ℝ≥0∞) < τ ∧
          0 < U (u n i) ∧ ENNReal.ofReal (U (u n i)) < C then
        Real.exp (-(q * (u n i : ℝ))) * ψ (U (u n i)) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0) := by
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i < n + 1 := Finset.mem_range.mp hi
  have hstep : (u n i : ℝ) ≤ (u n (i + 1) : ℝ) := by
    exact_mod_cast hmono n i hi'
  have hδ : 0 ≤ (u n (i + 1) : ℝ) - (u n i : ℝ) := sub_nonneg.mpr hstep
  by_cases hs : (u n i : ℝ≥0∞) < τ ∧
      0 < U (u n i) ∧ ENNReal.ofReal (U (u n i)) < C
  · have hc : (u n i : ℝ≥0∞) < τ ∧
        0 ≤ U (u n i) ∧ ENNReal.ofReal (U (u n i)) ≤ C :=
      ⟨hs.1, le_of_lt hs.2.1, le_of_lt hs.2.2⟩
    simp only [if_pos hs, if_pos hc, le_refl]
  · by_cases hc : (u n i : ℝ≥0∞) < τ ∧
        0 ≤ U (u n i) ∧ ENNReal.ofReal (U (u n i)) ≤ C
    · have hψi : ψ (U (u n i)) ≤ 0 := hψ _ hc.2.1 hc.2.2
      have he : 0 ≤ Real.exp (-(q * (u n i : ℝ))) :=
        le_of_lt (Real.exp_pos _)
      have hterm : Real.exp (-(q * (u n i : ℝ))) * ψ (U (u n i)) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ)) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos he hψi) hδ
      simpa only [if_pos hc, if_neg hs] using hterm
    · simp only [if_neg hc, if_neg hs, le_refl]
