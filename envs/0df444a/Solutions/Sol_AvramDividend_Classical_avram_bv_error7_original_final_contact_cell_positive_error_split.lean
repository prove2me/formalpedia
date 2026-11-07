-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_original_final_contact_cell_positive_error_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T10:01:17.755643+00:00
-- url     : https://prove2.me/submissions/14ee2ee9-e365-4728-b866-d1859bb44ca2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- In the actual stopped physical-grid BV C1 source, a final contact
cell contributes only its own positive Taylor residual to the error budget. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ) (ω : Ω)
    (u : ℕ → ℝ≥0) (k : ℕ) (hk : 0 < k) :
    (let J : ℝ≥0 → ℝ := fun t =>
      ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
      else 0
     let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
     let g : ℕ → ℝ := fun i =>
       Real.exp (-(q * (u i : ℝ))) *
         (w (x + X.X (u i) ω - rightLimit D (u i) ω +
             (Y (u (i+1)) - Y (u i))) -
           w (x + X.X (u i) ω - rightLimit D (u i) ω) -
           deriv w (x + X.X (u i) ω - rightLimit D (u i) ω) *
             (Y (u (i+1)) - Y (u i)))
     max (∑ i ∈ Finset.range k, g i) 0 ≤
       max (∑ i ∈ Finset.range (k - 1), g i) 0 +
         max (g (k - 1)) 0) := by
  have hFin (g : ℕ → ℝ) :
      max (∑ i ∈ Finset.range k, g i) 0 ≤
        max (∑ i ∈ Finset.range (k - 1), g i) 0 +
          max (g (k - 1)) 0 := by
    have hk' : k - 1 + 1 = k := Nat.sub_add_cancel hk
    rw [← hk', Finset.sum_range_succ]
    apply max_le
    · exact add_le_add (le_max_left _ _) (le_max_left _ _)
    · exact add_nonneg (le_max_right _ _) (le_max_right _ _)
  exact hFin _
