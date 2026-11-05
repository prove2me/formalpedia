-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_public_original_rate_from_compact_band_tests
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:36:34.193135+00:00
-- url     : https://prove2.me/submissions/cb73bbf3-74c9-478c-9f5a-8b6a2543385c

import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_separated_borel_nu_finite
import Mathlib.Topology.Order.LeftRightLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Finite original marked intensity matching compact tests identifies every separated Borel mark. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ε : ℝ) (hε : 0 < ε)
    (ρ : Measure ℝ)
    (hρ : ∀ B : Set ℝ, MeasurableSet B →
      ρ B = (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (1 : ℝ≥0) ×ˢ B) ∂P))
    (hρfin : ρ (Iic (-ε)) < ⊤)
    (hTests : ∀ g : CompactlySupportedContinuousMap ℝ ℝ,
      (∫ y : ℝ, g y ∂(ρ.restrict (Iic (-ε)))) =
      (∫ y : ℝ, g y ∂(X.ν.restrict (Iic (-ε))))) :
    ∀ B : Set ℝ, MeasurableSet B → B ⊆ Iic (-ε) →
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (1 : ℝ≥0) ×ˢ B) ∂P) = X.ν B := by
  have hνfin : X.ν (Iic (-ε)) < ⊤ :=
    avram_p2_a_zero_rate_separated_borel_nu_finite
      X (Iic (-ε)) measurableSet_Iic ε hε Subset.rfl
  have hνfinRestrict : (X.ν.restrict (Iic (-ε))) Set.univ < ⊤ := by
    simpa using hνfin
  have hρfinRestrict : (ρ.restrict (Iic (-ε))) Set.univ < ⊤ := by
    simpa using hρfin
  letI : IsFiniteMeasure (X.ν.restrict (Iic (-ε))) := ⟨hνfinRestrict⟩
  letI : IsFiniteMeasure (ρ.restrict (Iic (-ε))) := ⟨hρfinRestrict⟩
  letI : (X.ν.restrict (Iic (-ε))).Regular := inferInstance
  letI : (ρ.restrict (Iic (-ε))).Regular := inferInstance
  have heq : ρ.restrict (Iic (-ε)) = X.ν.restrict (Iic (-ε)) :=
    Measure.ext_of_integral_eq_on_compactlySupported hTests
  intro B hB hBsep
  have hρB : (ρ.restrict (Iic (-ε))) B = ρ B := by
    rw [Measure.restrict_apply hB, inter_eq_left.mpr hBsep]
  have hνB : (X.ν.restrict (Iic (-ε))) B = X.ν B := by
    rw [Measure.restrict_apply hB, inter_eq_left.mpr hBsep]
  calc
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (1 : ℝ≥0) ×ˢ B) ∂P) = ρ B := (hρ B hB).symm
    _ = (ρ.restrict (Iic (-ε))) B := hρB.symm
    _ = (X.ν.restrict (Iic (-ε))) B := by rw [heq]
    _ = X.ν B := hνB
