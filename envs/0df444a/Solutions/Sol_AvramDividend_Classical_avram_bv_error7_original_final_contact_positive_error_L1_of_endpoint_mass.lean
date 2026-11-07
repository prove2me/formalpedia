-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_original_final_contact_positive_error_L1_of_endpoint_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T00:00:39.651741+00:00
-- url     : https://prove2.me/submissions/5d0d011b-31e2-4c22-bbbf-d3027638236c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_final_contact_compensated_increment_ae_zero
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_discounted_single_contact_Taylor_bound
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_final_contact_Taylor_error_ae_zero_of_endpoint_bounds
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_final_contact_Taylor_error_le_BV_mass_of_endpoint_bounds
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_BV_mass_positive_DCT_for_random_errors
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The original final-contact Taylor error has L1-small positive part
from an actual BV source-mass dominator and one-cell endpoint bounds.
This is independent of the signed BV dividend prebudget. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q L : ℝ) (hq : 0 ≤ q) (hL : 0 ≤ L)
    (T : ℝ≥0) (hT : T ≤ 1)
    (u : ℕ → ℕ → ℝ≥0) (k : ℕ → Ω → ℕ)
    (hGrid : ∀ m ω, u m 0 = 0 ∧ u m (k m ω) ≤ T ∧
      (∀ i, i < k m ω → u m i ≤ u m (i + 1)))
    (hMesh : ∀ᵐ ω ∂P,
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       ∀ δ : ℝ, 0 < δ → ∀ᶠ m in Filter.atTop,
         ∀ i, i < k m ω →
           |Y (u m (i + 1)) - Y (u m i)| < δ))
    (hContact : ∀ m ω, k m ω ≠ 0 →
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       let z : ℝ := x + X.X (u m (k m ω - 1)) ω -
         rightLimit D (u m (k m ω - 1)) ω
       let c : ℝ := Y (u m (k m ω)) - Y (u m (k m ω - 1))
       |w (z + c) - w z| ≤ L * |c| ∧ |deriv w z| ≤ L))
    (Err : ℕ → Ω → ℝ)
    (hSource : ∀ m ω, Err m ω =
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       let z : ℝ := x + X.X (u m (k m ω - 1)) ω -
         rightLimit D (u m (k m ω - 1)) ω
       let c : ℝ := Y (u m (k m ω)) - Y (u m (k m ω - 1))
       if k m ω = 0 then 0
       else Real.exp (-(q * (u m (k m ω - 1) : ℝ))) *
         (w (z + c) - w z - deriv w z * c)))
    (hErrMeas : ∀ m, AEStronglyMeasurable (Err m) P) :
    (∀ m, Integrable (fun ω => max (Err m ω) 0) P) ∧
    Tendsto (fun m => ∫ ω, max (Err m ω) 0 ∂P)
      atTop (nhds (0 : ℝ)) := by
  have hAE :=
    avram_bv_error7_original_final_contact_Taylor_error_ae_zero_of_endpoint_bounds
      X x C D hD w q L hq hL u k hMesh hContact Err hSource
  have hDom :=
    avram_bv_error7_original_final_contact_Taylor_error_le_BV_mass_of_endpoint_bounds
      X hBV x C D hD w q L hq hL T u k hGrid hContact Err hSource
  exact avram_bv_error7_original_BV_mass_positive_DCT_for_random_errors
    X hX hBV T hT (2 * L) (by positivity) Err hErrMeas hAE hDom
