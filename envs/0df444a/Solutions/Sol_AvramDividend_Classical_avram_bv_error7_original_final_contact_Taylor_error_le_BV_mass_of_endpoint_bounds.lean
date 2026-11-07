-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_original_final_contact_Taylor_error_le_BV_mass_of_endpoint_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:50:34.758237+00:00
-- url     : https://prove2.me/submissions/998a0b51-e071-4dfa-870f-4ac8b8281e6d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_discounted_single_contact_Taylor_bound
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_final_contact_compensated_increment_le_BV_mass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The authentic single ruin/horizon contact Taylor remainder admits a
uniform integrable original BV source-mass envelope once the endpoint
value-change and initial derivative have a common one-cell bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q L : ℝ) (hq : 0 ≤ q) (hL : 0 ≤ L)
    (T : ℝ≥0) (u : ℕ → ℕ → ℝ≥0) (k : ℕ → Ω → ℕ)
    (hGrid : ∀ m ω, u m 0 = 0 ∧ u m (k m ω) ≤ T ∧
      (∀ i, i < k m ω → u m i ≤ u m (i + 1)))
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
         (w (z + c) - w z - deriv w z * c))) :
    ∀ m, ∀ᵐ ω ∂P,
      ‖Err m ω‖ ≤ (2 * L) * (|X.drift| * (T : ℝ) +
        |(T : ℝ) * X.drift - X.X T ω|) := by
  have hMass :=
    avram_bv_error7_original_final_contact_compensated_increment_le_BV_mass
      X hBV T u k hGrid
  intro m
  filter_upwards [hMass] with ω hω
  let inc : ℝ :=
    let J : ℝ≥0 → ℝ := fun t =>
      ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
      else 0
    let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
    if k m ω = 0 then 0
    else Y (u m (k m ω)) - Y (u m (k m ω - 1))
  have hCell : |Err m ω| ≤ (2 * L) * |inc| := by
    by_cases hk : k m ω = 0
    · rw [hSource m ω]
      simp [inc, hk]
    · obtain ⟨hLip, hDeriv⟩ := hContact m ω hk
      dsimp at hLip hDeriv
      have hOne := avram_bv_error7_discounted_single_contact_Taylor_bound
        w q (u m (k m ω - 1) : ℝ)
        (x + X.X (u m (k m ω - 1)) ω -
          rightLimit D (u m (k m ω - 1)) ω)
        ((X.X (u m (k m ω)) ω +
          (∑' v : ℝ≥0, if 0 < v ∧ v ≤ u m (k m ω) then
            Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
          else 0)) -
          (X.X (u m (k m ω - 1)) ω +
          (∑' v : ℝ≥0, if 0 < v ∧ v ≤ u m (k m ω - 1) then
            Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
          else 0))) L
        hq (u m (k m ω - 1)).property hL hLip hDeriv
      rw [hSource m ω]
      simpa only [inc, if_neg hk] using hOne
  have hMassNow : |inc| ≤
      |X.drift| * (T : ℝ) +
        |(T : ℝ) * X.drift - X.X T ω| := hω m
  change |Err m ω| ≤ (2 * L) *
    (|X.drift| * (T : ℝ) + |(T : ℝ) * X.drift - X.X T ω|)
  exact hCell.trans
    (mul_le_mul_of_nonneg_left hMassNow (by positivity))
