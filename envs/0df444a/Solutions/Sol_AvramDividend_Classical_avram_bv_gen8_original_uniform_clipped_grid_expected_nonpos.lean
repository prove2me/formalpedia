-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_gen8_original_uniform_clipped_grid_expected_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T17:39:19.556713+00:00
-- url     : https://prove2.me/submissions/0d8a52e9-1afc-4bb5-8113-e4d305f59a43

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_original_uniform_cell_clipped_hjb_L1
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
noncomputable section

/-- The exact clipped generator grid has finite L¹ and nonpositive mean. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (hgrid : ∀ n, u n 0 = 0 ∧
      ((u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2)))
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1))
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2))
    (K : ℝ) (hK : 0 ≤ K) :
    let B : ℕ → Ω → ℝ := fun n ω =>
      let Z : ℕ → ℝ := fun j => Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n j)
      ∑ i ∈ Finset.range (n + 1), max (-K) (
        if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
            0 < Z i ∧ ENNReal.ofReal (Z i) < C then
          Real.exp (-(q * (u n i : ℝ))) *
            (X.generator w (Z i) - q * w (Z i)) *
            ((u n (i + 1) : ℝ) - (u n i : ℝ))
        else 0)
    ∀ n, Integrable (B n) P ∧
      (∫ ω, B n ω ∂P) ≤ 0 := by
  let B : ℕ → Ω → ℝ := fun n ω =>
    let Z : ℕ → ℝ := fun j => Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n j)
    ∑ i ∈ Finset.range (n + 1), max (-K) (
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < Z i ∧ ENNReal.ofReal (Z i) < C then
        Real.exp (-(q * (u n i : ℝ))) *
          (X.generator w (Z i) - q * w (Z i)) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0)
  change ∀ n, Integrable (B n) P ∧ (∫ ω, B n ω ∂P) ≤ 0
  intro n
  have hInt : Integrable (B n) P := by
    change Integrable (fun ω => ∑ i ∈ Finset.range (n + 1),
      max (-K) (
        let Z : ℕ → ℝ := fun j => Function.leftLim
          (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n j)
        if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
            0 < Z i ∧ ENNReal.ofReal (Z i) < C then
          Real.exp (-(q * (u n i : ℝ))) *
            (X.generator w (Z i) - q * w (Z i)) *
            ((u n (i + 1) : ℝ) - (u n i : ℝ))
        else 0)) P
    apply integrable_finset_sum
    intro i hi
    exact avram_bv_gen8_original_uniform_cell_clipped_hjb_L1
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      T hT u hgrid hmono huniform K hK n i (Finset.mem_range.mp hi)
  have hPoint : ∀ ω, B n ω ≤ 0 := by
    intro ω
    let Z : ℕ → ℝ := fun i => Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
    change (∑ i ∈ Finset.range (n + 1), max (-K) (
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < Z i ∧ ENNReal.ofReal (Z i) < C then
        Real.exp (-(q * (u n i : ℝ))) *
          (X.generator w (Z i) - q * w (Z i)) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0)) ≤ 0
    apply Finset.sum_nonpos
    intro i hi
    split_ifs with h
    · have hGen : X.generator w (Z i) - q * w (Z i) ≤ 0 :=
        (hw_gen (Z i) h.2.1 h.2.2).2
      have hTime : 0 ≤ (u n (i + 1) : ℝ) - (u n i : ℝ) := by
        exact sub_nonneg.mpr (by exact_mod_cast hmono n i (Finset.mem_range.mp hi))
      have hCell : Real.exp (-(q * (u n i : ℝ))) *
          (X.generator w (Z i) - q * w (Z i)) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ)) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos (le_of_lt (Real.exp_pos _)) hGen) hTime
      exact max_le (neg_nonpos.mpr hK) hCell
    · exact max_le (neg_nonpos.mpr hK) (le_refl (0 : ℝ))
  constructor
  · exact hInt
  · apply integral_nonpos_of_ae
    exact Filter.Eventually.of_forall hPoint