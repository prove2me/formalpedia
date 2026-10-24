-- Prove2me | solution 1 for AvramDividend.Classical.capped_surviving_terminal_test_integrable_of_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T22:57:31.516786+00:00
-- url     : https://prove2.me/submissions/81fcb062-aa66-4ef8-8812-3a3d441e50df

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_continuous_test_abs_le_on_finite_cap
import Theorems.Thm_AvramDividend_Classical_capped_riskProcess_range_before_ruin_including_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- A measurable terminal HJB test is integrable under a finite reserve cap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (B : ℝ) (hB : 0 ≤ B)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal B)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal B) D)
    (τ : Ω → ℝ≥0)
    (hMeas : AEStronglyMeasurable
      (fun ω => if ((τ ω : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω then
        w (riskProcess X x D (τ ω) ω) else 0) P) :
    Integrable (fun ω => if ((τ ω : ℝ≥0) : ℝ≥0∞) <
      ruinTime X x D ω then
      w (riskProcess X x D (τ ω) ω) else 0) P := by
  haveI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨M, hM0, hM⟩ :=
    continuous_test_abs_le_on_finite_cap w B hB hw
  apply Integrable.of_bound hMeas M
  apply Filter.Eventually.of_forall
  intro ω
  change ‖if ((τ ω : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω then
    w (riskProcess X x D (τ ω) ω) else 0‖ ≤ M
  split_ifs with hSurvive
  · obtain ⟨hNonneg, hCap⟩ :=
      capped_riskProcess_range_before_ruin_including_zero
        X x hx (ENNReal.ofReal B) hxc D hD ω (τ ω) hSurvive
    have hUpper : riskProcess X x D (τ ω) ω ≤ B :=
      (ENNReal.ofReal_le_ofReal_iff hB).mp hCap
    simpa only [Real.norm_eq_abs] using hM _ hNonneg hUpper
  · simpa only [norm_zero] using hM0
