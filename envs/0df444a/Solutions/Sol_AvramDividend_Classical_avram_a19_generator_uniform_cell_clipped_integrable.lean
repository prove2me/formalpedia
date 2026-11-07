-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_generator_uniform_cell_clipped_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:52:56.858422+00:00
-- url     : https://prove2.me/submissions/3dd6f60b-49d3-4350-b4b8-798302b50121

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_a19_generator_uniform_cell_active_set_measurable
import Theorems.Thm_AvramDividend_Classical_avram_a19_generator_uniform_cell_factor_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Every clipped stopped original generator cell is integrable. -/
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
    (K : ℝ) (hK : 0 ≤ K)
    (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (hgrid : ∀ n, u n 0 = 0 ∧
      ((u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2)))
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1))
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2)) :
    ∀ n i, i < n + 1 → Integrable (fun ω => max (
      let Z : ℕ → ℝ := fun j => Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n j)
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < Z i ∧ ENNReal.ofReal (Z i) < C then
        Real.exp (-(q * (u n i : ℝ))) *
          (X.generator w (Z i) - q * w (Z i)) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0) (-K)) P := by
  intro n i hii
  let F : Ω → ℝ := fun ω =>
    let Z : ℕ → ℝ := fun j => Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n j)
    if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
        0 < Z i ∧ ENNReal.ofReal (Z i) < C then
      Real.exp (-(q * (u n i : ℝ))) *
        (X.generator w (Z i) - q * w (Z i)) *
        ((u n (i + 1) : ℝ) - (u n i : ℝ))
    else 0
  have hactive := avram_a19_generator_uniform_cell_active_set_measurable
    X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
    hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
    T hT u hgrid hmono huniform n i hii
  have hfactor := avram_a19_generator_uniform_cell_factor_measurable
    X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
    hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
    T hT u hgrid hmono huniform n i hii
  have hFm : Measurable F := by
    exact Measurable.ite hactive hfactor measurable_const
  have hFle : ∀ ω, F ω ≤ 0 := by
    intro ω
    let Z : ℕ → ℝ := fun j => Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n j)
    change (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
      0 < Z i ∧ ENNReal.ofReal (Z i) < C then
      Real.exp (-(q * (u n i : ℝ))) *
        (X.generator w (Z i) - q * w (Z i)) *
        ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0) ≤ 0
    split_ifs with h
    · have hg := (hw_gen (Z i) h.2.1 h.2.2).2
      have hwidth :
          (0 : ℝ) ≤ (u n (i + 1) : ℝ) - (u n i : ℝ) := by
        have hm : (u n i : ℝ) ≤ (u n (i + 1) : ℝ) := by
          exact_mod_cast hmono n i hii
        exact sub_nonneg.mpr hm
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos
          (le_of_lt (Real.exp_pos _)) hg) hwidth
    · exact le_refl 0
  change Integrable (fun ω => max (F ω) (-K)) P
  letI : IsProbabilityMeasure P := X.isProbability
  refine ⟨(hFm.max measurable_const).aestronglyMeasurable, ?_⟩
  refine HasFiniteIntegral.of_bounded (C := K) ?_
  apply Filter.Eventually.of_forall
  intro ω
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨le_max_right _ _,
    (max_le (hFle ω) (neg_nonpos.mpr hK)).trans hK⟩
