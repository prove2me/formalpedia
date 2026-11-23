-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_f2_original_discounted_controlled_reserve_four_way_grid_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T00:39:02.126468+00:00
-- url     : https://prove2.me/submissions/c9f91a11-816c-41a5-bcc9-5152046ad4d5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Exact original-reserve four-way finite-grid split into drift, residual BV R, negative jumps and dividends. -/
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
    let U : ℝ≥0 → ℝ := fun t =>
      x + X.X t ω - rightLimit D t ω
    let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
    (∑ i ∈ Finset.range n,
      e i * (deriv w (U (u i)) * (U (u (i + 1)) - U (u i)))) =
      (∑ i ∈ Finset.range n,
        e i * (deriv w (U (u i)) *
          (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift))) -
      (∑ i ∈ Finset.range n,
        e i * (deriv w (U (u i)) * (R (u (i + 1)) - R (u i)))) -
      (∑ i ∈ Finset.range n,
        e i * (deriv w (U (u i)) * (J (u (i + 1)) - J (u i)))) -
      (∑ i ∈ Finset.range n,
        e i * (deriv w (U (u i)) *
          (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω))) := by
  intro J Y R U e
  have hReserveCell (i : ℕ) :
      U (u (i + 1)) - U (u i) =
        (Y (u (i + 1)) - Y (u i)) -
        (J (u (i + 1)) - J (u i)) -
        (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω) := by
    dsimp only [U, Y]
    ring
  have hYCell (i : ℕ) :
      Y (u (i + 1)) - Y (u i) =
        (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift) -
        (R (u (i + 1)) - R (u i)) := by
    dsimp only [Y, R]
    ring
  have hCell (i : ℕ) :
      U (u (i + 1)) - U (u i) =
        (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift) -
        (R (u (i + 1)) - R (u i)) -
        (J (u (i + 1)) - J (u i)) -
        (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω) := by
    rw [hReserveCell i, hYCell i]
  calc
    (∑ i ∈ Finset.range n,
      e i * (deriv w (U (u i)) * (U (u (i + 1)) - U (u i)))) =
      (∑ i ∈ Finset.range n,
        e i * (deriv w (U (u i)) *
          (((((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift) -
            (R (u (i + 1)) - R (u i))) -
            (J (u (i + 1)) - J (u i)) -
            (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω)))) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hCell i]
    _ = (∑ i ∈ Finset.range n,
        e i * (deriv w (U (u i)) *
          (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift))) -
      (∑ i ∈ Finset.range n,
        e i * (deriv w (U (u i)) * (R (u (i + 1)) - R (u i)))) -
      (∑ i ∈ Finset.range n,
        e i * (deriv w (U (u i)) * (J (u (i + 1)) - J (u i)))) -
      (∑ i ∈ Finset.range n,
        e i * (deriv w (U (u i)) *
          (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω))) := by
      simp only [mul_sub, Finset.sum_sub_distrib]
