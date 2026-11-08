-- Prove2me | solution 1 for AvramDividend.Classical.avram_coord8_original_masked_deriv_R_grid_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T16:56:26.043599+00:00
-- url     : https://prove2.me/submissions/5abe3164-4ceb-465e-8bf3-b1287a2952ea

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_a19_nonint_original_masked_derivative_grid_cell_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_coordinatewise_weighted_R_mesh_L1
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_stopped_clipped_derivative_mesh_L1

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original masked derivative residual is integrable if its finitely many
    coefficients obey a uniform bound. -/
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
    (n : ℕ) (S : ℝ≥0) (huS : u n (n + 1) ≤ S)
    (K : ℝ) (hK : 0 ≤ K)
    (hBound : ∀ ω i, i < n + 1 →
      |(if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < Function.leftLim (fun t : ℝ≥0 =>
            x + X.X t ω - rightLimit D t ω) (u n i) ∧
          ENNReal.ofReal (Function.leftLim (fun t : ℝ≥0 =>
            x + X.X t ω - rightLimit D t ω) (u n i)) < C then
        Real.exp (-(q * (u n i : ℝ))) *
          deriv w (Function.leftLim (fun t : ℝ≥0 =>
            x + X.X t ω - rightLimit D t ω) (u n i))
       else 0)| ≤ K) :
    Integrable (fun ω =>
      let Z : ℕ → ℝ := fun i => Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) -
          ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
          else 0
      ∑ i ∈ Finset.range (n + 1),
        (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
            0 < Z i ∧ ENNReal.ofReal (Z i) < C then
          Real.exp (-(q * (u n i : ℝ))) * deriv w (Z i)
         else 0) * (R (u n i) - R (u n (i + 1)))) P := by
  have hInt := avram_bv_residual10_original_stopped_clipped_derivative_mesh_L1
    X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen
      hw_grad x hx hxc D hD hw_nonneg hjump T hT u hgrid hmono
      huniform n K hK
  convert hInt using 1
  funext ω
  dsimp only
  apply Finset.sum_congr rfl
  intro i hi
  have hsmall : i < n + 1 := Finset.mem_range.mp hi
  have hcoef := hBound ω i hsmall
  simp only [if_pos hsmall, if_pos hcoef]
