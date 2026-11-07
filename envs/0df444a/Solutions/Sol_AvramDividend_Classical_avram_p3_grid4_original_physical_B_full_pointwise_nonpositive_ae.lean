-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_original_physical_B_full_pointwise_nonpositive_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T17:45:50.749892+00:00
-- url     : https://prove2.me/submissions/3b9aea12-ed52-44a4-b4d4-4a08b41dae3c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_physical_HJB_cell_sum_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_residual_continuous_monotone_locally_BV
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The exact original generator and BV-residual source B is a.s. nonpositive. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (u : ℕ → ℝ≥0) (n : ℕ)
    (hmono : ∀ i, i < n + 1 → u i ≤ u (i + 1)) :
    ∀ᵐ ω ∂P,
      let Z : ℕ → ℝ := fun i => Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u i)
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      (∑ i ∈ Finset.range (n + 1),
        if (u i : ℝ≥0∞) < ruinTime X x D ω ∧
            0 < Z i ∧ ENNReal.ofReal (Z i) < C then
          Real.exp (-(q * (u i : ℝ))) *
            (X.generator w (Z i) - q * w (Z i)) *
            ((u (i + 1) : ℝ) - (u i : ℝ))
        else 0) +
      (∑ i ∈ Finset.range (n + 1),
        (if (u i : ℝ≥0∞) < ruinTime X x D ω ∧
            0 < Z i ∧ ENNReal.ofReal (Z i) < C then
          Real.exp (-(q * (u i : ℝ))) * deriv w (Z i)
         else 0) * (R (u i) - R (u (i + 1)))) ≤ 0 := by
  filter_upwards
    [avram_p3_a_bvdrift_original_raw_residual_continuous_monotone_locally_BV X hBV]
    with ω hω
  rcases hω with ⟨_, hmonoR, _⟩
  dsimp
  let Z : ℕ → ℝ := fun i => Function.leftLim
    (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u i)
  have hgen :
      (∑ i ∈ Finset.range (n + 1),
        if (u i : ℝ≥0∞) < ruinTime X x D ω ∧
            0 < Z i ∧ ENNReal.ofReal (Z i) < C then
          Real.exp (-(q * (u i : ℝ))) *
            (X.generator w (Z i) - q * w (Z i)) *
            ((u (i + 1) : ℝ) - (u i : ℝ))
        else 0) ≤ 0 := by
    simpa [Z] using
      (avram_p3_grid4_original_physical_HJB_cell_sum_nonpos
        X q w C hw_gen x D ω u n hmono)
  have hres :
      (∑ i ∈ Finset.range (n + 1),
        (if (u i : ℝ≥0∞) < ruinTime X x D ω ∧
            0 < Z i ∧ ENNReal.ofReal (Z i) < C then
          Real.exp (-(q * (u i : ℝ))) * deriv w (Z i)
         else 0) *
          (((u i : ℝ) * X.drift - X.X (u i) ω -
            (∑' v : ℝ≥0, if 0 < v ∧ v ≤ u i then
              Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
            else 0)) -
            ((u (i + 1) : ℝ) * X.drift - X.X (u (i + 1)) ω -
              (∑' v : ℝ≥0, if 0 < v ∧ v ≤ u (i + 1) then
                Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
              else 0)))) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i hi
    by_cases hc : (u i : ℝ≥0∞) < ruinTime X x D ω ∧
        0 < Z i ∧ ENNReal.ofReal (Z i) < C
    · simp only [if_pos hc]
      have hgrad : 0 ≤ deriv w (Z i) :=
        le_trans (by norm_num : (0 : ℝ) ≤ 1) (hw_grad (Z i) hc.2.1 hc.2.2)
      apply mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (le_of_lt (Real.exp_pos _)) hgrad)
      exact sub_nonpos.mpr (hmonoR (hmono i (Finset.mem_range.mp hi)))
    · simp [hc]
  exact add_nonpos hgen hres
