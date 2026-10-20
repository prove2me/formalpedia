-- Prove2me | solution 1 for AvramDividend.Classical.chat03_noexit_uniformIntegrable_of_measurable_event
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T23:05:45.903391+00:00
-- url     : https://prove2.me/submissions/6ead50d5-408b-487a-9574-48863f2cd447

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_noexit_payoff_family_uniformIntegrable
import Theorems.Thm_AvramDividend_Classical_chat03_scale_function_borel_measurable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
The no-exit payoff is uniformly integrable once the infinite-passage
event is measurable. This discharges the family measurability premise of
the earlier proved conditional uniform-integrability theorem.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (hEvent : MeasurableSet
      {ω : Ω | twoSidedExitUpTime X (a - x) ω = ∞ ∧
        twoSidedExitDownTime X (-x) ω = ∞}) :
    UniformIntegrable
      (fun t : ℝ≥0 => fun ω : Ω =>
        if twoSidedExitUpTime X (a - x) ω = ∞ ∧
           twoSidedExitDownTime X (-x) ω = ∞ then
          Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω)
        else 0)
      (1 : ℝ≥0∞) P := by
  have hWmeas : Measurable W :=
    chat03_scale_function_borel_measurable X q W hW
  have hMeas : ∀ t : ℝ≥0,
      AEStronglyMeasurable
        (fun ω : Ω =>
          if twoSidedExitUpTime X (a - x) ω = ∞ ∧
             twoSidedExitDownTime X (-x) ω = ∞ then
            Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω)
          else 0) P := by
    intro t
    have hXt : Measurable (X.X t) :=
      (X.adapted t).mono (𝓕.le t) le_rfl
    have hVal : Measurable (fun ω : Ω => W (x + X.X t ω)) :=
      hWmeas.comp (measurable_const.add hXt)
    have hPay : Measurable (fun ω : Ω =>
        Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω)) :=
      measurable_const.mul hVal
    exact (Measurable.ite hEvent hPay measurable_const).aestronglyMeasurable
  exact chat03_noexit_payoff_family_uniformIntegrable
    X q hq W hW a x ha hx0 hxa
    (fun t ω =>
      if twoSidedExitUpTime X (a - x) ω = ∞ ∧
         twoSidedExitDownTime X (-x) ω = ∞ then
        Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω)
      else 0)
    (by intros; rfl) hMeas

