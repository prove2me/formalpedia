-- Prove2me | solution 1 for AvramDividend.Classical.lintegral_le_of_null_nonpositive_and_positive_truncation_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T20:58:59.575043+00:00
-- url     : https://prove2.me/submissions/bfb62d63-a41e-4c9b-8d84-55878679c336

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (μ : Measure ℝ)
    (hzero : μ (Set.Iic (0 : ℝ)) = 0)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) (B : ℝ≥0∞)
    (hbound : ∀ n : ℕ,
      (∫⁻ r, if r ∈ Set.Ioc (0 : ℝ) (n : ℝ) then f r else 0 ∂μ) ≤ B) :
    (∫⁻ r, f r ∂μ) ≤ B := by
  let g : ℕ → ℝ → ℝ≥0∞ := fun n r =>
    if r ∈ Set.Ioc (0 : ℝ) (n : ℝ) then f r else 0
  have hmeas : ∀ n : ℕ, Measurable (g n) := by
    intro n
    exact Measurable.ite measurableSet_Ioc hf measurable_const
  have hmono : Monotone g := by
    intro n m hnm r
    change (if r ∈ Set.Ioc (0 : ℝ) (n : ℝ) then f r else 0) ≤
      (if r ∈ Set.Ioc (0 : ℝ) (m : ℝ) then f r else 0)
    by_cases hn : r ∈ Set.Ioc (0 : ℝ) (n : ℝ)
    · have hnm' : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
      have hm : r ∈ Set.Ioc (0 : ℝ) (m : ℝ) :=
        ⟨hn.1, hn.2.trans hnm'⟩
      simp only [if_pos hn, if_pos hm, le_refl]
    · simp only [if_neg hn]
      exact zero_le
  have hsup (r : ℝ) (hr : 0 < r) : (⨆ n, g n r) = f r := by
    apply le_antisymm
    · apply iSup_le
      intro n
      dsimp [g]
      split_ifs
      · exact le_refl _
      · exact zero_le
    · obtain ⟨n, hn⟩ := exists_nat_gt r
      have hmem : r ∈ Set.Ioc (0 : ℝ) (n : ℝ) :=
        ⟨hr, le_of_lt hn⟩
      calc
        f r = g n r := by
          dsimp [g]
          rw [if_pos hmem]
        _ ≤ ⨆ k, g k r := le_iSup_of_le n le_rfl
  have hae : ∀ᵐ r ∂μ, r ∉ Set.Iic (0 : ℝ) :=
    measure_eq_zero_iff_ae_notMem.mp hzero
  have heq : (∫⁻ r, f r ∂μ) =
      (∫⁻ r, ⨆ n, g n r ∂μ) := by
    apply lintegral_congr_ae
    filter_upwards [hae] with r hr
    exact (hsup r (lt_of_not_ge hr)).symm
  calc
    (∫⁻ r, f r ∂μ) = ∫⁻ r, ⨆ n, g n r ∂μ := heq
    _ = ⨆ n, ∫⁻ r, g n r ∂μ := lintegral_iSup hmeas hmono
    _ ≤ B := by
      apply iSup_le
      intro n
      exact hbound n
