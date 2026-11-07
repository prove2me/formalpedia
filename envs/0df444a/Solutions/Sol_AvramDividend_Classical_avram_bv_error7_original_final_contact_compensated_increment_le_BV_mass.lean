-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_original_final_contact_compensated_increment_le_BV_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:41:23.536202+00:00
-- url     : https://prove2.me/submissions/cdc4b593-d7ab-4c30-aa49-c66f39cf3d28

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_Y_grid_variation_le_integrable_source_mass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The genuine original stopped final compensated Y-cell is controlled by
the same finite-horizon BV source mass used for the interior Taylor errors.
The last cell may touch ruin or the cap and k=0 has exactly zero mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (u : ℕ → ℕ → ℝ≥0)
    (k : ℕ → Ω → ℕ)
    (hGrid : ∀ m ω, u m 0 = 0 ∧ u m (k m ω) ≤ T ∧
      (∀ i, i < k m ω → u m i ≤ u m (i + 1))) :
    ∀ᵐ ω ∂P, ∀ m,
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       |if k m ω = 0 then (0 : ℝ)
        else Y (u m (k m ω)) - Y (u m (k m ω - 1))| ≤
         |X.drift| * (T : ℝ) +
           |(T : ℝ) * X.drift - X.X T ω|) := by
  filter_upwards
    [avram_bv_error7_original_Y_grid_variation_le_integrable_source_mass
      X hBV T] with ω hω
  intro m
  let J : ℝ≥0 → ℝ := fun t =>
    ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
      Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
    else 0
  let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
  change |if k m ω = 0 then (0 : ℝ)
      else Y (u m (k m ω)) - Y (u m (k m ω - 1))| ≤
        |X.drift| * (T : ℝ) +
          |(T : ℝ) * X.drift - X.X T ω|
  by_cases hk : k m ω = 0
  · simp [hk]
    positivity
  · obtain ⟨h0, hEnd, hMono⟩ := hGrid m ω
    have hPrevIndex : k m ω - 1 < k m ω := by omega
    have hNextIndex : k m ω - 1 + 1 = k m ω := by omega
    have hPrev : u m (k m ω - 1) ≤ u m (k m ω) := by
      simpa only [hNextIndex] using hMono (k m ω - 1) hPrevIndex
    let v : ℕ → ℝ≥0 := fun i =>
      if i = 0 then 0 else
      if i = 1 then u m (k m ω - 1) else
      if i = 2 then u m (k m ω) else T
    have hv0 : v 0 = 0 := by simp [v]
    have hv3 : v 3 = T := by simp [v]
    have hvMono : ∀ i, i < 3 → v i ≤ v (i + 1) := by
      intro i hi
      interval_cases i <;> simp [v, hPrev, hEnd]
    have hVar := hω v 3 hv0 hv3 hvMono
    have hTerm : |Y (v 2) - Y (v 1)| ≤
        ∑ i ∈ Finset.range 3, |Y (v (i + 1)) - Y (v i)| := by
      have hOne : (1 : ℕ) ∈ Finset.range 3 := by decide
      simpa using (Finset.single_le_sum
        (fun i hi => abs_nonneg (Y (v (i + 1)) - Y (v i))) hOne)
    rw [if_neg hk]
    change |Y (v 2) - Y (v 1)| ≤
      |X.drift| * (T : ℝ) + |(T : ℝ) * X.drift - X.X T ω|
    exact hTerm.trans hVar
