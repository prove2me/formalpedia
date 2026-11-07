-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_original_Y_grid_variation_le_integrable_source_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T09:01:24.925535+00:00
-- url     : https://prove2.me/submissions/9fe6634e-9583-430d-94f9-e206ae97d0b4

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_BV_all_Y_physical_grid_variation
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_negative_jump_tsum_nonnegative
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Every original BV physical-grid increment of the jump-removed Y has
total variation bounded by an L1-source mass, with no proxy process. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0) (n : ℕ),
      u 0 = 0 → u n = T →
      (∀ i, i < n → u i ≤ u (i + 1)) →
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       (∑ i ∈ Finset.range n,
         |Y (u (i + 1)) - Y (u i)|) ≤
          |X.drift| * (T : ℝ) +
            |(T : ℝ) * X.drift - X.X T ω|) := by
  filter_upwards
    [avram_p3_f2_original_BV_all_Y_physical_grid_variation X hBV]
      with ω hω
  intro u n hu0 hun hmono
  let J : ℝ≥0 → ℝ := fun t =>
    ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
      Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
    else 0
  let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
  let R : ℝ≥0 → ℝ := fun t =>
    ((t : ℝ) * X.drift - X.X t ω) - J t
  have hvar : (∑ i ∈ Finset.range n,
      |Y (u (i + 1)) - Y (u i)|) ≤
      |X.drift| * ((u n : ℝ) - (u 0 : ℝ)) +
        (R (u n) - R (u 0)) := hω u n hmono
  have hJ : 0 ≤ J T := by
    simpa only [J] using
      (avram_p3_a_bvdrift_original_raw_negative_jump_tsum_nonnegative
        X ω 0 T (by positivity))
  have hJ0 : J 0 = 0 := by
    have hTerm (v : ℝ≥0) :
        (if 0 < v ∧ v ≤ 0 then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0) = (0 : ℝ) := by
      split_ifs with hv
      · exact ((not_lt_of_ge hv.2) hv.1).elim
      · rfl
    simp only [J, hTerm]
    simp
  have hR0 : R 0 = 0 := by
    simp [R, hJ0, X.X_zero]
  change (∑ i ∈ Finset.range n,
    |Y (u (i + 1)) - Y (u i)|) ≤
    |X.drift| * (T : ℝ) + |(T : ℝ) * X.drift - X.X T ω|
  calc
    _ ≤ |X.drift| * ((u n : ℝ) - (u 0 : ℝ)) +
        (R (u n) - R (u 0)) := hvar
    _ = |X.drift| * (T : ℝ) +
        ((T : ℝ) * X.drift - X.X T ω - J T) := by
      simp [hu0, hun, hR0, R]
    _ ≤ |X.drift| * (T : ℝ) +
        |(T : ℝ) * X.drift - X.X T ω| := by
      have hraw := le_abs_self ((T : ℝ) * X.drift - X.X T ω)
      linarith
