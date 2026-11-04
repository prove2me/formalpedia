-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_UBV_admissible_finitecap_physical_boundary_weight_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T17:09:31.496928+00:00
-- url     : https://prove2.me/submissions/33949c6f-a85c-45c6-b316-6cecb0a2d4a6

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_ruin_stopped_lebesgue_zero_cap_contact_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original UBV admissibility assumptions directly remove discounted
    physical-time occupation of the two endpoints, with no claim about
    singular Stieltjes dividend mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (hx : 0 ≤ x) (hc : 0 ≤ c)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal c)
    (τ : Ω → ℝ≥0∞)
    (hτ : ∀ ω, τ ω ≤ ruinTime X x D ω)
    (μ : Measure ℝ≥0) [SFinite μ] (hZeroMass : μ {0} = 0)
    (weight : ℝ≥0 → Ω → ℝ≥0∞) :
    ∀ᵐ ω ∂P,
      (∫⁻ t : ℝ≥0,
        if (t : ℝ≥0∞) < τ ω ∧
          (riskProcess X x D t ω = 0 ∨ riskProcess X x D t ω = c)
        then weight t ω else 0 ∂μ) = 0 := by
  have hDiv : IsDividendStrategy 𝓕 D := hD.1.1
  have hxcReal : x ≤ c :=
    (ENNReal.ofReal_le_ofReal_iff hc).mp hxc
  have hZero : ∀ ω, riskProcess X x D 0 ω ≤ c := by
    intro ω
    simpa [riskProcess, X.X_zero ω, hDiv.1 ω] using hxcReal
  have hCap : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω →
      riskProcess X x D s ω ≤ c := by
    intro ω s hs
    by_cases hs0 : s = 0
    · simpa [hs0] using hZero ω
    · have hspos : 0 < s := pos_iff_ne_zero.mpr hs0
      exact (ENNReal.ofReal_le_ofReal_iff hc).mp (hD.2 ω s hspos)
  exact
    avram_p4_e_localise_original_ruin_stopped_lebesgue_zero_cap_contact_zero
      X hBV x c D hD hDiv hCap τ hτ μ hZeroMass weight
