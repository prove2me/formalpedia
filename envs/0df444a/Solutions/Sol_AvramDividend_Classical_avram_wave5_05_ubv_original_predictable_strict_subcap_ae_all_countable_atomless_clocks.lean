-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_05_ubv_original_predictable_strict_subcap_ae_all_countable_atomless_clocks
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:47:36.077824+00:00
-- url     : https://prove2.me/submissions/53b3e8b2-cfe7-4585-b0a0-868e1a93879e

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_strict_subcap_ae_on_atomless_clock

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

/-!
One original controlled UBV event supports strict subcap
predictable reserve at almost every positive pre-ruin time of
EVERY prescribed clock in a countable atomless family.
-/

/-- True predictable cap strictness on all countable clocks. -/
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
    (hatom : ∀ n, NullSingletonClass (μ n)) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ᵐ t : ℝ≥0 ∂μ n,
      0 < t → (t : ℝ≥0∞) < ruinTime X x D ω →
        Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t < c := by
  apply (ae_all_iff).2
  intro n
  letI : SFinite (μ n) := hsf n
  letI : NullSingletonClass (μ n) := hatom n
  exact avram_wave5_05_ubv_original_predictable_strict_subcap_ae_on_atomless_clock
    X hBV x c D hD hCap (μ n)
