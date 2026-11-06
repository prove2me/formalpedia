-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_f2_original_discounted_Y_drift_minus_R_physical_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T00:33:26.712667+00:00
-- url     : https://prove2.me/submissions/20a0e7b3-dd4d-46d2-9b02-730a46884b1c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The true discounted source Y derivative grid is exactly the Lévy drift grid minus its original R variation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q : ℝ) (ω : Ω)
    (u : ℕ → ℝ≥0) (n : ℕ) :
    let J : ℝ≥0 → ℝ := fun t =>
      ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
    let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
    let R : ℝ≥0 → ℝ := fun t =>
      ((t : ℝ) * X.drift - X.X t ω) - J t
    let z : ℕ → ℝ := fun i =>
      x + X.X (u i) ω - rightLimit D (u i) ω
    let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
    (∑ i ∈ Finset.range n,
      e i * (deriv w (z i) * (Y (u (i + 1)) - Y (u i)))) =
      (∑ i ∈ Finset.range n,
        e i * (deriv w (z i) *
          (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift))) -
      (∑ i ∈ Finset.range n,
        e i * (deriv w (z i) * (R (u (i + 1)) - R (u i)))) := by
  intro J Y R z e
  have hCell (i : ℕ) :
      Y (u (i + 1)) - Y (u i) =
        (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift) -
          (R (u (i + 1)) - R (u i)) := by
    dsimp only [Y, R]
    ring
  calc
    (∑ i ∈ Finset.range n,
      e i * (deriv w (z i) * (Y (u (i + 1)) - Y (u i)))) =
      (∑ i ∈ Finset.range n,
        e i * (deriv w (z i) *
          ((((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift) -
            (R (u (i + 1)) - R (u i))))) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hCell i]
    _ = (∑ i ∈ Finset.range n,
        e i * (deriv w (z i) *
          (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift))) -
      (∑ i ∈ Finset.range n,
        e i * (deriv w (z i) * (R (u (i + 1)) - R (u i)))) := by
      simp only [mul_sub, Finset.sum_sub_distrib]
