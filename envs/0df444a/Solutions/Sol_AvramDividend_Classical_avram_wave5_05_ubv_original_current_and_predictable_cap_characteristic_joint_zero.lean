-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_05_ubv_original_current_and_predictable_cap_characteristic_joint_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T11:47:37.880411+00:00
-- url     : https://prove2.me/submissions/21a147dc-6693-48d5-8569-153559fb02fd

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_same_source_weighted_cap_contact_clock_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_cap_contact_weighted_atomless_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

/-!
The same original UBV trajectory has two chronological source-state
arguments: current reserve U_t and predictable pre-event reserve U-.
Their cap-characteristic densities simultaneously vanish on the
identical atomless clock; no assumption on dividend-payment location.
-/

/-- Original cap-current and cap-predictable characteristic clocks are
    both null on one original-process conull event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (hCap : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω → riskProcess X x D s ω ≤ c)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ]
    (currentWeight preWeight : ℝ≥0 → Ω → ℝ≥0∞) :
    ∀ᵐ ω ∂P,
      (∫⁻ t : ℝ≥0,
        if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω ∧
            riskProcess X x D t ω = c
        then currentWeight t ω else 0 ∂μ) = 0 ∧
      (∫⁻ t : ℝ≥0,
        if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω ∧
            Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t = c
        then preWeight t ω else 0 ∂μ) = 0 := by
  have hCurrent :=
    avram_wave5_05_ubv_same_source_weighted_cap_contact_clock_zero
      X hBV x c D hD hCap μ currentWeight
  have hPre :=
    avram_wave5_05_ubv_original_predictable_cap_contact_weighted_atomless_zero
      X hBV x c D hD hCap μ preWeight
  filter_upwards [hCurrent, hPre] with ω hc hp
  exact ⟨hc, hp⟩
