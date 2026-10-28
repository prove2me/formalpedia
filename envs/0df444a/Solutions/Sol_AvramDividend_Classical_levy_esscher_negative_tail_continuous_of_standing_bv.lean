-- Prove2me | solution 1 for AvramDividend.Classical.levy_esscher_negative_tail_continuous_of_standing_bv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T07:41:21.251832+00:00
-- url     : https://prove2.me/submissions/c36efd5d-ad53-4d3a-a078-60ae1c7b7943

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levyMeasure_singleton_null_of_standing_boundedVariation
import Theorems.Thm_AvramDividend_Classical_levy_negative_mass_away_from_zero_finite
import Theorems.Thm_AvramDividend_Classical_continuousOn_esscher_weighted_negative_tail_of_finite_noAtoms
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

/-- Under BV standing assumptions, an Esscher tilt leaves the negative jump-tail
    intensity continuous at every strictly positive jump-size threshold. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hbv : X.BoundedVariation) (φ : ℝ) (hφ : 0 ≤ φ) :
    ContinuousOn (fun r : ℝ =>
      (X.ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y)))).real (Iic (-r)))
      (Ioi (0 : ℝ)) := by
  letI : NullSingletonClass X.ν :=
    ⟨fun a => levyMeasure_singleton_null_of_standing_boundedVariation X hX hbv a⟩
  have hfinite : ∀ a : ℝ, a < 0 →
      (X.ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y)))) (Iic a) ≠ ⊤ := by
    intro a ha
    have hδ : 0 < -a := neg_pos.mpr ha
    have hmass : X.ν (Iic a) < ⊤ := by
      simpa using (levy_negative_mass_away_from_zero_finite X (-a) hδ)
    have hweight : ∀ᵐ y ∂(X.ν.restrict (Iic a)),
        ENNReal.ofReal (Real.exp (φ * y)) ≤ (1 : ENNReal) := by
      filter_upwards [ae_restrict_mem measurableSet_Iic] with y hy
      have hy0 : y ≤ 0 := le_trans hy (le_of_lt ha)
      have hmul : φ * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hφ hy0
      have hexp : Real.exp (φ * y) ≤ 1 := Real.exp_le_one_iff.mpr hmul
      simpa using (ENNReal.ofReal_le_ofReal hexp)
    have hbound :
        (X.ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y)))) (Iic a)
          ≤ X.ν (Iic a) := by
      rw [withDensity_apply _ measurableSet_Iic]
      calc
        (∫⁻ y in Iic a, ENNReal.ofReal (Real.exp (φ * y)) ∂X.ν)
            ≤ (∫⁻ y in Iic a, (1 : ENNReal) ∂X.ν) := lintegral_mono_ae hweight
        _ = X.ν (Iic a) := by simp
    exact ne_of_lt (lt_of_le_of_lt hbound hmass)
  exact continuousOn_esscher_weighted_negative_tail_of_finite_noAtoms X.ν φ hfinite
