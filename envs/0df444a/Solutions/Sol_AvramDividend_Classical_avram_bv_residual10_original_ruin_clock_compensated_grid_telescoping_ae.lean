-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual10_original_ruin_clock_compensated_grid_telescoping_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T22:51:08.530961+00:00
-- url     : https://prove2.me/submissions/f8af4d1b-00fe-442c-8037-7db0bd0a1c48

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_ruin_clock_stopped_compensated_path_ae

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The authentic stopped BV compensated source telescopes on each finite
physical grid exactly to its drift-weighted stopped endpoint difference. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (S : ℝ≥0)
    (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i,
      (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2)) :
    ∀ᵐ ω ∂P, ∀ n : ℕ,
      let τ : ℝ≥0 :=
        (min (ruinTime X x D ω) (S : ℝ≥0∞)).toNNReal
      let J : ℝ≥0 → ℝ := fun r =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ r then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
      let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
      (∑ i ∈ Finset.range (n + 1),
        (Y (min (u n (i + 1)) τ) - Y (min (u n i) τ))) =
          (((min (u n (n + 1)) τ : ℝ≥0) : ℝ) -
            ((min (u n 0) τ : ℝ≥0) : ℝ)) * X.drift := by
  filter_upwards [avram_bv_residual10_original_ruin_clock_stopped_compensated_path_ae
    X hX hBV x D S] with ω hω
  intro n
  let τ : ℝ≥0 :=
    (min (ruinTime X x D ω) (S : ℝ≥0∞)).toNNReal
  let J : ℝ≥0 → ℝ := fun r =>
    ∑' v : ℝ≥0, if 0 < v ∧ v ≤ r then
      Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
    else 0
  let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
  have hstop (t : ℝ≥0) :
      Y (min t τ) = ((min t τ : ℝ≥0) : ℝ) * X.drift := hω t
  calc
    (∑ i ∈ Finset.range (n + 1),
        (Y (min (u n (i + 1)) τ) - Y (min (u n i) τ))) =
      Y (min (u n (n + 1)) τ) - Y (min (u n 0) τ) := by
        exact Finset.sum_range_sub (fun i => Y (min (u n i) τ)) (n + 1)
    _ = (((min (u n (n + 1)) τ : ℝ≥0) : ℝ) -
          ((min (u n 0) τ : ℝ≥0) : ℝ)) * X.drift := by
        rw [hstop (u n (n + 1)), hstop (u n 0)]
        ring
