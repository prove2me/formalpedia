-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual10_original_stopped_derivative_R_mesh_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T14:23:46.733645+00:00
-- url     : https://prove2.me/submissions/3e19d57d-1009-4d29-8d14-7a366d20fc51

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_discounted_interior_residual_mesh_nonpositive

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact stopped derivative-weighted original BV raw R mesh contribution
is nonpositive almost surely, with no global derivative upper bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (u : ℕ → ℕ → ℝ≥0) (n : ℕ)
    (hu : ∀ i, i < n + 1 → u n i ≤ u n (i + 1)) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      (∑ i ∈ Finset.range (n + 1),
        (let Z := Function.leftLim
          (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
         if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
             0 < Z ∧ ENNReal.ofReal Z < C then
           Real.exp (-(q * (u n i : ℝ))) * deriv w Z
         else 0) * (R (u n i) - R (u n (i + 1)))) ≤ 0 := by
  classical
  let v : ℕ → ℝ≥0 := u n
  let Z : ℕ → Ω → ℝ := fun i ω =>
    if (u n i : ℝ≥0∞) < ruinTime X x D ω then
      Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
    else 0
  have hs := avram_p3_bv_original_discounted_interior_residual_mesh_nonpositive
    X hBV v (n + 1) hu q C w hw_grad Z
  filter_upwards [hs] with ω hsω
  apply (le_of_eq ?_).trans hsω
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hτ : (u n i : ℝ≥0∞) < ruinTime X x D ω
  · simp [Z, v, hτ]
  · simp [Z, v, hτ]
