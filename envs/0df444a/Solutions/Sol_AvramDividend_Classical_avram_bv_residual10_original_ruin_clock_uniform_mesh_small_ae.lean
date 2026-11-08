-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual10_original_ruin_clock_uniform_mesh_small_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T22:37:31.720339+00:00
-- url     : https://prove2.me/submissions/704bc19c-a558-4340-9e99-1f08e2588e7c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_ruin_clock_stopped_compensated_path_ae
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_uniform_stopped_cell_width_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original BV drift-plus-negative-jump path has uniformly small
increments on the physical grid stopped at the authentic bounded ruin clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (S : ℝ≥0)
    (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i,
      (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2)) :
    ∀ᵐ ω ∂P,
      let τ : ℝ≥0 :=
        (min (ruinTime X x D ω) (S : ℝ≥0∞)).toNNReal
      let J : ℝ≥0 → ℝ := fun r =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ r then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
      let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
      (∀ n i,
        |Y (min (u n (i + 1)) τ) - Y (min (u n i) τ)| ≤
          |X.drift| * (T / ((n : ℝ) + 2))) ∧
      (∀ δ : ℝ, 0 < δ →
        ∀ᶠ n in atTop, ∀ i,
          |Y (min (u n (i + 1)) τ) - Y (min (u n i) τ)| < δ) := by
  filter_upwards [avram_bv_residual10_original_ruin_clock_stopped_compensated_path_ae
    X hX hBV x D S] with ω hω
  let τ : ℝ≥0 :=
    (min (ruinTime X x D ω) (S : ℝ≥0∞)).toNNReal
  let J : ℝ≥0 → ℝ := fun r =>
    ∑' v : ℝ≥0, if 0 < v ∧ v ≤ r then
      Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
    else 0
  let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
  have hstop (t : ℝ≥0) :
      Y (min t τ) = ((min t τ : ℝ≥0) : ℝ) * X.drift := by
    exact hω t
  have hcell (n i : ℕ) :
      |Y (min (u n (i + 1)) τ) - Y (min (u n i) τ)| ≤
        |X.drift| * (T / ((n : ℝ) + 2)) := by
    rw [hstop (u n (i + 1)), hstop (u n i)]
    simp only [NNReal.coe_min]
    have hw := avram_bv_residual10_uniform_stopped_cell_width_bound
      T hT u huniform (τ : ℝ) n i
    calc
      |min (u n (i + 1) : ℝ) (τ : ℝ) * X.drift -
          min (u n i : ℝ) (τ : ℝ) * X.drift| =
          |X.drift| *
            (min (u n (i + 1) : ℝ) (τ : ℝ) -
              min (u n i : ℝ) (τ : ℝ)) := by
            rw [← sub_mul, abs_mul, abs_of_nonneg hw.1]
            ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hw.2 (abs_nonneg _)
  refine ⟨hcell, ?_⟩
  intro δ hδ
  obtain ⟨N, hN⟩ : ∃ N : ℕ, |X.drift| * T / δ < (N : ℝ) :=
    exists_nat_gt _
  filter_upwards [eventually_ge_atTop N] with n hn
  intro i
  have hnR : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hden : 0 < (n : ℝ) + 2 := by positivity
  have hN' : |X.drift| * T < δ * (N : ℝ) := by
    nlinarith [(div_lt_iff₀ hδ).mp hN]
  have hnum : |X.drift| * T < δ * ((n : ℝ) + 2) := by
    nlinarith
  calc
    |Y (min (u n (i + 1)) τ) - Y (min (u n i) τ)| ≤
        |X.drift| * (T / ((n : ℝ) + 2)) := hcell n i
    _ = |X.drift| * T / ((n : ℝ) + 2) := by ring
    _ < δ := (div_lt_iff₀ hden).2 hnum
