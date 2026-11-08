-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual10_original_stopped_clipped_derivative_mesh_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T13:02:00.535215+00:00
-- url     : https://prove2.me/submissions/960ef87c-8ac6-4f80-afb6-c39b07edf67e

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_a19_nonint_original_masked_derivative_grid_cell_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_clipped_weighted_R_mesh_L1

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact original stopped, discounted derivative coefficient admits
finite-level integrable raw Levy residual sums after coefficient clipping. -/
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
    (n : ℕ) (K : ℝ) (hK : 0 ≤ K) :
    Integrable (fun ω =>
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      let Z : ℕ → ℝ := fun i => Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      ∑ i ∈ Finset.range (n + 1),
        (let a : ℝ :=
          if i < n + 1 then
            if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
                0 < Z i ∧ ENNReal.ofReal (Z i) < C then
              Real.exp (-(q * (u n i : ℝ))) * deriv w (Z i)
            else 0
          else 0
         if |a| ≤ K then a else 0) *
          (R (u n i) - R (u n (i + 1)))) P := by
  classical
  let a : Ω → ℕ → ℝ := fun ω i =>
    if i < n + 1 then
      let Z := Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < Z ∧ ENNReal.ofReal Z < C then
        Real.exp (-(q * (u n i : ℝ))) * deriv w Z
      else 0
    else 0
  have hMeasA : ∀ i, Measurable (fun ω => a ω i) := by
    intro i
    by_cases hi : i < n + 1
    · have hc := avram_a19_nonint_original_masked_derivative_grid_cell_measurable
        X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad
        x hx hxc D hD hw_nonneg hjump T hT u hgrid hmono huniform n i hi
      simpa only [a, if_pos hi] using hc
    · have hzero : (fun ω => a ω i) = fun _ : Ω => (0 : ℝ) := by
        funext ω
        simp only [a, if_neg hi]
      rw [hzero]
      exact measurable_const
  let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
  have hEnd : u n (n + 1) ≤ S := by
    have hfrac : 0 ≤ T / ((n : ℝ) + 2) := by positivity
    have hh : (u n (n + 1) : ℝ) ≤ T := by
      calc
        _ = T - T / ((n : ℝ) + 2) := (hgrid n).2
        _ ≤ T := sub_le_self _ hfrac
    exact_mod_cast hh
  have hInt := avram_bv_residual10_original_clipped_weighted_R_mesh_L1
    X hX hBV S u n (hmono n) (hgrid n).1 hEnd a hMeasA K hK
  convert hInt using 1
