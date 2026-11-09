-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_tail12_original_grid_B_nonpositive_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T13:41:08.98229+00:00
-- url     : https://prove2.me/submissions/5f26c926-c00c-452a-a52f-07a279ba1695

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_weighted_grid_residual_zero_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (u : ℕ → ℕ → ℝ≥0)
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1))
    (Z : ℕ → Ω → ℕ → ℝ) (good : ℕ → Ω → ℕ → Prop)
    (hgood : ∀ n ω i, good n ω i →
      0 < Z n ω i ∧ ENNReal.ofReal (Z n ω i) < C)
    (A : ℕ → Ω → ℕ → ℝ) (B : ℕ → Ω → ℝ)
    (hB : ∀ n ω, B n ω =
      (∑ i ∈ Finset.range (n + 1),
        if good n ω i then
          Real.exp (-(q * (u n i : ℝ))) *
            (X.generator w (Z n ω i) - q * w (Z n ω i)) *
            ((u n (i + 1) : ℝ) - (u n i : ℝ))
        else 0) +
      (let J : ℝ≥0 → ℝ := fun t =>
         ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
           Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
         else 0
       let R : ℝ≥0 → ℝ := fun t =>
         ((t : ℝ) * X.drift - X.X t ω) - J t
       ∑ i ∈ Finset.range (n + 1),
         A n ω i * (R (u n i) - R (u n (i + 1))))) :
    ∀ᵐ ω ∂P, ∀ n, B n ω ≤ 0 := by
  classical
  filter_upwards [avram_bv_residual10_original_weighted_grid_residual_zero_ae
    X hX hBV u A] with ω hR
  intro n
  have hsum : (∑ i ∈ Finset.range (n + 1),
      if good n ω i then
        Real.exp (-(q * (u n i : ℝ))) *
          (X.generator w (Z n ω i) - q * w (Z n ω i)) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i hi
    by_cases hg : good n ω i
    · simp only [if_pos hg]
      have hpos := (hgood n ω i hg).1
      have hcap := (hgood n ω i hg).2
      have hG := (hw_gen (Z n ω i) hpos hcap).2
      have he : 0 ≤ Real.exp (-(q * (u n i : ℝ))) :=
        (Real.exp_pos _).le
      have ht : (u n i : ℝ) ≤ (u n (i + 1) : ℝ) := by
        exact_mod_cast hmono n i (Finset.mem_range.mp hi)
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos he hG) (sub_nonneg.mpr ht)
    · simp only [if_neg hg]
      exact le_refl 0
  simpa only [hB n ω, hR n, add_zero] using hsum
