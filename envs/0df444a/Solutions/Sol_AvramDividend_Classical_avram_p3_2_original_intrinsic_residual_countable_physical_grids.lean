-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_intrinsic_residual_countable_physical_grids
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T16:31:55.004933+00:00
-- url     : https://prove2.me/submissions/0d3e3780-8011-4b0b-b0b5-dbf685d25603

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_explicit_ruin_cap_BV_residual
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- A single full-probability original-X event works for every physical
ruin-clipped mesh in a countable refining family, including cap contact. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (q : ℝ) (T : ℝ≥0) (u : ℕ → ℕ → ℝ≥0)
    (hu : ∀ m, Monotone (u m)) (n : ℕ → ℕ) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)
    ∀ᵐ ω ∂P, ∀ m : ℕ,
      let τ : ℝ≥0 := (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
      let v : ℕ → ℝ≥0 := fun i => min (u m i) τ
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) -
          (∑' s : ℝ≥0, if 0 < s ∧ s ≤ t then
            ENNReal.ofReal
              (Function.leftLim (fun z : ℝ≥0 => X.X z ω) s - X.X s ω)
            else 0).toReal
      Monotone R ∧
        (∑ i : Fin (n m),
          Real.exp (-(q * (v i : ℝ))) *
            (V (riskProcess X x D (v i) ω -
              (R (v (i + 1)) - R (v i))) -
             V (riskProcess X x D (v i) ω))) ≤ 0 := by
  apply ae_all_iff.mpr
  intro m
  exact avram_p3_2_original_explicit_ruin_cap_BV_residual
    X hBV x D w C hC hw_cont hw0 hw_neg hw_smooth hw_grad
    q T (u m) (hu m) (n m)
