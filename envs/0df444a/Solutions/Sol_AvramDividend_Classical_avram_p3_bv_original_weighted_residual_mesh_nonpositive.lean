-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_weighted_residual_mesh_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:26:03.790657+00:00
-- url     : https://prove2.me/submissions/d547a24c-519d-4c6f-b4d2-591b0a5da5a2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/- On the original source path, the BV residual remaining after physical
drift and actual negative source jumps has nonnegative increments. It
therefore contributes nonpositively to every positively weighted mesh. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (u : ℕ → ℝ≥0) (n : ℕ)
    (hGrid : ∀ i : ℕ, i < n → u i ≤ u (i + 1))
    (W : ℕ → Ω → ℝ)
    (hW : ∀ ω (i : ℕ), i < n → 0 ≤ W i ω) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      (∑ i ∈ Finset.range n,
        W i ω * (R (u i) - R (u (i + 1)))) ≤ 0 := by
  filter_upwards
    [avram_p3_a_bvdrift_original_raw_removed_residual_monotone X hBV]
    with ω hR
  dsimp only
  let J : ℝ≥0 → ℝ := fun t =>
    ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
      Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
    else 0
  let R : ℝ≥0 → ℝ := fun t =>
    ((t : ℝ) * X.drift - X.X t ω) - J t
  have hRmon : Monotone R := hR
  apply Finset.sum_nonpos
  intro i hi
  have hi' : i < n := Finset.mem_range.mp hi
  have hRstep : R (u i) ≤ R (u (i + 1)) :=
    hRmon (hGrid i hi')
  exact mul_nonpos_of_nonneg_of_nonpos (hW ω i hi')
    (sub_nonpos.mpr hRstep)
