-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux9_original_uniform_grid_total_B_ae_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T09:14:03.827514+00:00
-- url     : https://prove2.me/submissions/b436d6f3-eb6f-4588-b72d-923c23e26873

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_monotone
import Theorems.Thm_AvramDividend_Classical_avram_a19_original_physical_generator_drift_sum_nonpos
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
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2)) :
    ∀ B : ℕ → Ω → ℝ,
      (∀ n ω,
        let Z : ℕ → ℝ := fun i => Function.leftLim
          (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
        B n ω =
          (∑ i ∈ Finset.range (n + 1),
            if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
                0 < Z i ∧ ENNReal.ofReal (Z i) < C then
              Real.exp (-(q * (u n i : ℝ))) *
                (X.generator w (Z i) - q * w (Z i)) *
                ((u n (i + 1) : ℝ) - (u n i : ℝ))
            else 0) +
          (let J : ℝ≥0 → ℝ := fun t =>
            ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
              Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
            else 0
           let R : ℝ≥0 → ℝ := fun t =>
            ((t : ℝ) * X.drift - X.X t ω) - J t
           ∑ i ∈ Finset.range (n + 1),
             (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
                 0 < Z i ∧ ENNReal.ofReal (Z i) < C then
               Real.exp (-(q * (u n i : ℝ))) * deriv w (Z i)
             else 0) * (R (u n i) - R (u n (i + 1))))) →
      ∀ᵐ ω ∂P, ∀ n, B n ω ≤ 0 := by
  intro B hBdef
  filter_upwards [avram_p3_a_bvdrift_original_raw_removed_residual_monotone X hBV] with ω hMono
  intro n
  let Z : ℕ → ℝ := fun i =>
    Function.leftLim (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
  let J : ℝ≥0 → ℝ := fun t =>
    ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
      Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
    else 0
  let R : ℝ≥0 → ℝ := fun t =>
    ((t : ℝ) * X.drift - X.X t ω) - J t
  let W : ℕ → ℝ := fun i =>
    if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
        0 < Z i ∧ ENNReal.ofReal (Z i) < C then
      Real.exp (-(q * (u n i : ℝ))) * deriv w (Z i)
    else 0
  have hRmono : Monotone R := hMono
  have hW (i : ℕ) : 0 ≤ W i := by
    dsimp [W]
    split_ifs with hi
    · have hd : 0 ≤ deriv w (Z i) :=
        le_trans (by norm_num) (hw_grad (Z i) hi.2.1 hi.2.2)
      exact mul_nonneg (le_of_lt (Real.exp_pos _)) hd
    · exact le_refl _
  have hRes : (∑ i ∈ Finset.range (n + 1),
    W i * (R (u n i) - R (u n (i + 1)))) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i hi
    have hu := hmono n i (Finset.mem_range.mp hi)
    exact mul_nonpos_of_nonneg_of_nonpos (hW i)
      (sub_nonpos.mpr (hRmono hu))
  have hGen : (∑ i ∈ Finset.range (n + 1),
            if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
                0 < Z i ∧ ENNReal.ofReal (Z i) < C then
              Real.exp (-(q * (u n i : ℝ))) *
                (X.generator w (Z i) - q * w (Z i)) *
                ((u n (i + 1) : ℝ) - (u n i : ℝ))
            else 0) ≤ 0 :=
    avram_a19_original_physical_generator_drift_sum_nonpos
      X q w C hw_gen x D u hmono n ω
  have hExact : B n ω = (∑ i ∈ Finset.range (n + 1),
            if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
                0 < Z i ∧ ENNReal.ofReal (Z i) < C then
              Real.exp (-(q * (u n i : ℝ))) *
                (X.generator w (Z i) - q * w (Z i)) *
                ((u n (i + 1) : ℝ) - (u n i : ℝ))
            else 0) + (∑ i ∈ Finset.range (n + 1),
    W i * (R (u n i) - R (u n (i + 1)))) := hBdef n ω
  linarith
