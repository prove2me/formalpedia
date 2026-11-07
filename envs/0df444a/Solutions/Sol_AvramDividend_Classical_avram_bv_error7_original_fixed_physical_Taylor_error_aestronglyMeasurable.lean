-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_original_fixed_physical_Taylor_error_aestronglyMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T19:04:05.290201+00:00
-- url     : https://prove2.me/submissions/c1fd35e9-9804-47c8-b377-a2f702d1246b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_measurable
import Theorems.Thm_AvramDividend_Classical_avram_route11_original_raw_jump_cumulative_aestronglyMeasurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_fixed_physical_Taylor_error_measurable_of_evaluations
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The original stopped deterministic-grid C1 Taylor error is measurable from
X adaptedness, D right-limit measurability and the genuine BV J evaluation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw : Measurable w)
    (hderiv : Measurable (deriv w))
    (q : ℝ) (u : ℕ → ℕ → ℝ≥0) (k : ℕ → ℕ)
    (Err : ℕ → Ω → ℝ)
    (hSource : ∀ m ω, Err m ω =
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       let z : ℕ → ℝ := fun i =>
         x + X.X (u m i) ω - rightLimit D (u m i) ω
       let c : ℕ → ℝ := fun i => Y (u m (i + 1)) - Y (u m i)
       ∑ i ∈ Finset.range (k m),
         Real.exp (-(q * (u m i : ℝ))) *
           (w (z i + c i) - w (z i) - deriv w (z i) * c i))) :
    ∀ m, AEStronglyMeasurable (Err m) P := by
  have hXeval (m i : ℕ) :
      AEStronglyMeasurable (fun ω => X.X (u m i) ω) P := by
    have hm : Measurable (fun ω => X.X (u m i) ω) :=
      (X.adapted (u m i)).mono (𝓕.le (u m i)) le_rfl
    exact hm.aestronglyMeasurable
  have hDeval (m i : ℕ) :
      AEStronglyMeasurable (fun ω => rightLimit D (u m i) ω) P :=
    (dividendStrategy_rightLimit_measurable
      D hD.1.1 (u m i)).aestronglyMeasurable
  have hJeval (m i : ℕ) :
      AEStronglyMeasurable
        (fun ω => ∑' v : ℝ≥0, if 0 < v ∧ v ≤ u m i then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
          else 0) P :=
    avram_route11_original_raw_jump_cumulative_aestronglyMeasurable
      X hX hBV (u m i)
  exact avram_bv_error7_original_fixed_physical_Taylor_error_measurable_of_evaluations
    X x C D hD w hw hderiv q u k
    hXeval hDeval hJeval Err hSource
