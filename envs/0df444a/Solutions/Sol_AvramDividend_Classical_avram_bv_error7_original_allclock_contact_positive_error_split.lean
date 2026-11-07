-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_original_allclock_contact_positive_error_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T10:05:31.190839+00:00
-- url     : https://prove2.me/submissions/2e63b532-3731-44c9-8d03-e7c4c8ba525f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_final_contact_cell_positive_error_split
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The original zero-clock stopped grid has no terminal contact residual;
positive-error splitting holds uniformly for every finite grid length. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ) (ω : Ω)
    (u : ℕ → ℝ≥0) (k : ℕ) :
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
         (if k = 0 then 0 else max (g (k - 1)) 0)) := by
  by_cases hk : k = 0
  · subst k
    simp
  · have hkPos : 0 < k := Nat.pos_of_ne_zero hk
    simpa [hk] using
      (avram_bv_error7_original_final_contact_cell_positive_error_split
        X x D w q ω u k hkPos)
