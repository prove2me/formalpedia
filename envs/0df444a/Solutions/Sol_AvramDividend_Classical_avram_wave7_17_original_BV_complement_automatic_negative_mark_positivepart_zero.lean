-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_17_original_BV_complement_automatic_negative_mark_positivepart_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:19:05.153565+00:00
-- url     : https://prove2.me/submissions/798e83a8-b7a4-43fb-a7f0-3bf6c703f35e

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_BV_ruin_stopped_strict_interior_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_BV_complement_stopped_negative_source_mark_positivepart_lintegral_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- The original finite physical clock times negative Lévy marks needs no
extra measurable-set assumption for the stopped value-drop sign. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (H : ℝ) (hH : 0 ≤ H)
    (hEnvelope : ¬ (x + H * X.drift ≤ w x))
    (T : ℝ≥0) :
    let μ : Measure ((ℝ≥0 × Ω) × ℝ) :=
      (((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal).prod P).prod X.ν)
    let Y : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim (fun t : ℝ≥0 =>
        x + X.X t p.2 - rightLimit D t p.2) p.1
    let S : Set ((ℝ≥0 × Ω) × ℝ) :=
      {p | p.1.1 ≤ T ∧
        (p.1.1 : ℝ≥0∞) < ruinTime X x D p.1.2 ∧
        0 < Y p.1 ∧ ENNReal.ofReal (Y p.1) < C ∧ p.2 < 0}
    (∫⁻ p in S, ENNReal.ofReal
      (Real.exp (-(q * (p.1.1 : ℝ))) *
        (w (Y p.1 + p.2) - w (Y p.1))) ∂μ) = 0 := by
  have hBase : MeasurableSet
      {p : ℝ≥0 × Ω |
        p.1 ≤ T ∧ (p.1 : ℝ≥0∞) < ruinTime X x D p.2 ∧
        0 < Function.leftLim (fun t : ℝ≥0 =>
          x + X.X t p.2 - rightLimit D t p.2) p.1 ∧
        ENNReal.ofReal (Function.leftLim (fun t : ℝ≥0 =>
          x + X.X t p.2 - rightLimit D t p.2) p.1) < C} :=
    avram_wave7_17_original_BV_ruin_stopped_strict_interior_measurable
      X x D hD.1.1 T C
  have hMark : MeasurableSet
      {p : ((ℝ≥0 × Ω) × ℝ) |
        p.1.1 ≤ T ∧ (p.1.1 : ℝ≥0∞) < ruinTime X x D p.1.2 ∧
        0 < Function.leftLim (fun t : ℝ≥0 =>
          x + X.X t p.1.2 - rightLimit D t p.1.2) p.1.1 ∧
        ENNReal.ofReal (Function.leftLim (fun t : ℝ≥0 =>
          x + X.X t p.1.2 - rightLimit D t p.1.2) p.1.1) < C ∧
        p.2 < 0} := by
    convert hBase.prod (measurableSet_Iio : MeasurableSet (Iio (0 : ℝ))) using 1
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_Iio]
    tauto
  exact avram_wave7_17_original_BV_complement_stopped_negative_source_mark_positivepart_lintegral_zero
    X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_grad
    x hx hxc D hD H hH hEnvelope T hMark
