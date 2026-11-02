-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_05_ubv_original_predictable_cap_zero_countably_many_atomless_clocks
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T11:44:44.918792+00:00
-- url     : https://prove2.me/submissions/b29ebb90-2392-4cfd-ba06-73aa932a6fc0

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_cap_contact_weighted_atomless_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

/-!
Countably many atomless physical-time generator characteristic clocks can
share a single almost-sure event of zero genuine predictable cap contact.
This is used for all levels of an original controlled Ito localisation.
-/

/-- Zero original predictable cap-contact mass, simultaneously for any
    prescribed countable collection of atomless s-finite clocks and weights. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (hCap : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω → riskProcess X x D s ω ≤ c)
    (μ : ℕ → Measure ℝ≥0)
    (hsf : ∀ n, SFinite (μ n))
    (hatom : ∀ n, NullSingletonClass (μ n))
    (weight : ℕ → ℝ≥0 → Ω → ℝ≥0∞) :
    ∀ᵐ ω ∂P, ∀ n : ℕ,
      (∫⁻ t : ℝ≥0,
        if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω ∧
            Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t = c
        then weight n t ω else 0 ∂μ n) = 0 := by
  apply (ae_all_iff).2
  intro n
  letI : SFinite (μ n) := hsf n
  letI : NullSingletonClass (μ n) := hatom n
  exact avram_wave5_05_ubv_original_predictable_cap_contact_weighted_atomless_zero
    X hBV x c D hD hCap (μ n) (weight n)
