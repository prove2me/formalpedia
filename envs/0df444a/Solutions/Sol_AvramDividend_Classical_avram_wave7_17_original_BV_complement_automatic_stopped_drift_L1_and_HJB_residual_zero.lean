-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_17_original_BV_complement_automatic_stopped_drift_L1_and_HJB_residual_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:16:15.369586+00:00
-- url     : https://prove2.me/submissions/8f227161-c6ee-4936-93da-64cb33876587

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_BV_ruin_stopped_strict_interior_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_BV_stopped_physical_discounted_drift_L1
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_BV_complement_stopped_interior_positive_drift_residual_lintegral_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- On the actual strict ruin-stopped source clock, the physical drift is
L¹ and the discounted positive HJB drift/jump residual has zero mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (H : ℝ) (hH : 0 ≤ H)
    (hEnvelope : ¬ (x + H * X.drift ≤ w x))
    (T : ℝ≥0) :
    let μ : Measure (ℝ≥0 × Ω) :=
      ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal).prod P)
    let Y : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim (fun t : ℝ≥0 =>
        x + X.X t p.2 - rightLimit D t p.2) p.1
    let S : Set (ℝ≥0 × Ω) :=
      {p | p.1 ≤ T ∧ (p.1 : ℝ≥0∞) < ruinTime X x D p.2 ∧
        0 < Y p ∧ ENNReal.ofReal (Y p) < C}
    IntegrableOn
      (fun p => Real.exp (-(q * (p.1 : ℝ))) * X.drift) S μ ∧
    (∫⁻ p in S, ENNReal.ofReal
      (Real.exp (-(q * (p.1 : ℝ))) *
        (X.drift + (∫ z in Iio (0 : ℝ),
          w (Y p + z) - w (Y p) ∂X.ν) - q * w (Y p))) ∂μ) = 0 := by
  have hStrategy : IsDividendStrategy 𝓕 D := hD.1.1
  have hS : MeasurableSet
      {p : ℝ≥0 × Ω |
        p.1 ≤ T ∧ (p.1 : ℝ≥0∞) < ruinTime X x D p.2 ∧
        0 < Function.leftLim (fun t : ℝ≥0 =>
          x + X.X t p.2 - rightLimit D t p.2) p.1 ∧
        ENNReal.ofReal (Function.leftLim (fun t : ℝ≥0 =>
          x + X.X t p.2 - rightLimit D t p.2) p.1) < C} :=
    avram_wave7_17_original_BV_ruin_stopped_strict_interior_measurable
      X x D hStrategy T C
  dsimp only
  constructor
  · exact avram_wave7_17_original_BV_stopped_physical_discounted_drift_L1
      X q (le_of_lt hq) x D T C hS
  · exact avram_wave7_17_original_BV_complement_stopped_interior_positive_drift_residual_lintegral_zero
      X hX hBV q hq w C hC hw_cont hw0 hw_smooth hw_gen hw_grad
      x hx hxc D hD H hH hEnvelope T hS
