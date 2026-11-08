-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid17_original_masked_derivative_R_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T22:07:34.085113+00:00
-- url     : https://prove2.me/submissions/fa0f01c5-76e2-4d30-b2f7-805783a3e19e

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_a19_nonint_original_masked_derivative_grid_cell_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid17_original_event_local_BV_weighted_residual_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- The genuine stopped derivative-weighted original BV residual is integrable
    on any measurable finite-grid event bounding its actual coefficients. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (hgrid : ∀ n, u n 0 = 0 ∧
      (u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2))
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1))
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2))
    (n : ℕ) (S : ℝ≥0) (hS : u n (n + 1) ≤ S)
    (s : Set Ω) (hs : MeasurableSet s) (K : ℝ) (hK : 0 ≤ K)
    (hBound : ∀ ω ∈ s, ∀ i < n + 1,
      |(if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
            0 < Function.leftLim (fun t : ℝ≥0 =>
              x + X.X t ω - rightLimit D t ω) (u n i) ∧
            ENNReal.ofReal (Function.leftLim (fun t : ℝ≥0 =>
              x + X.X t ω - rightLimit D t ω) (u n i)) < C then
          Real.exp (-(q * (u n i : ℝ))) *
            deriv w (Function.leftLim (fun t : ℝ≥0 =>
              x + X.X t ω - rightLimit D t ω) (u n i))
        else 0)| ≤ K) :
    Integrable (fun ω => if ω ∈ s then
      let Z : ℕ → ℝ := fun i => Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) -
          (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
          else 0)
      ∑ i ∈ Finset.range (n + 1),
        (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
            0 < Z i ∧ ENNReal.ofReal (Z i) < C then
          Real.exp (-(q * (u n i : ℝ))) * deriv w (Z i)
        else 0) * (R (u n i) - R (u n (i + 1)))
    else 0) P := by
  classical
  let a : Ω → ℕ → ℝ := fun ω i =>
    if hi : i ∈ Finset.range (n + 1) then
      let Z := Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < Z ∧ ENNReal.ofReal Z < C then
        Real.exp (-(q * (u n i : ℝ))) * deriv w Z else 0
    else 0
  have hMeas (i : ℕ) : Measurable (fun ω => a ω i) := by
    by_cases hi : i ∈ Finset.range (n + 1)
    · simpa only [a, dif_pos hi] using
        (avram_a19_nonint_original_masked_derivative_grid_cell_measurable
          X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen
          hw_grad x hx hxc D hD hw_nonneg hjump T hT u hgrid hmono huniform
          n i (Finset.mem_range.mp hi))
    · simpa only [a, dif_neg hi] using
        (measurable_const : Measurable (fun _ : Ω => (0 : ℝ)))
  have haBound (ω : Ω) (hω : ω ∈ s) (i : ℕ)
      (hi : i ∈ Finset.range (n + 1)) : |a ω i| ≤ K := by
    simpa only [a, dif_pos hi] using
      hBound ω hω i (Finset.mem_range.mp hi)
  have hBase :=
    avram_p3_grid17_original_event_local_BV_weighted_residual_integrable
      X hX hBV S u n (hmono n) (hgrid n).1 hS
      a hMeas s hs K hK haBound
  let R : Ω → ℝ≥0 → ℝ := fun ω t =>
    ((t : ℝ) * X.drift - X.X t ω) -
      (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
      else 0)
  have hEqual (ω : Ω) :
      (∑ i ∈ Finset.range (n + 1),
        a ω i * (R ω (u n i) - R ω (u n (i + 1)))) =
      (∑ i ∈ Finset.range (n + 1),
        (let Z := Function.leftLim
          (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
         if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
             0 < Z ∧ ENNReal.ofReal Z < C then
           Real.exp (-(q * (u n i : ℝ))) * deriv w Z else 0) *
        (R ω (u n i) - R ω (u n (i + 1)))) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [a, dif_pos hi]
  change Integrable (fun ω => if ω ∈ s then
    ∑ i ∈ Finset.range (n + 1),
      (let Z := Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
       if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
           0 < Z ∧ ENNReal.ofReal Z < C then
         Real.exp (-(q * (u n i : ℝ))) * deriv w Z else 0) *
      (R ω (u n i) - R ω (u n (i + 1))) else 0) P
  have heq :
      (fun ω => if ω ∈ s then
        ∑ i ∈ Finset.range (n + 1),
          (let Z := Function.leftLim
            (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
           if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
               0 < Z ∧ ENNReal.ofReal Z < C then
             Real.exp (-(q * (u n i : ℝ))) * deriv w Z else 0) *
          (R ω (u n i) - R ω (u n (i + 1))) else 0) =
      (fun ω => if ω ∈ s then
        ∑ i ∈ Finset.range (n + 1),
          a ω i * (R ω (u n i) - R ω (u n (i + 1))) else 0) := by
    funext ω
    by_cases hω : ω ∈ s
    · simp only [if_pos hω]
      exact (hEqual ω).symm
    · simp only [if_neg hω]
  rw [heq]
  exact hBase
