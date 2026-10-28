-- Prove2me | solution 1 for AvramDividend.Classical.chat04_full_history_killed_scale_payoff_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T20:05:06.269627+00:00
-- url     : https://prove2.me/submissions/775bcb96-11e6-41d2-9e0f-de8fad9b505d

import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_closed_survival_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_scaleFunction_measurable_of_punctured_continuity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable
open AvramDividend.Classical

/-- The full-history continuously killed q-scale terminal payoff is measurable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : Ω → ℝ) (hH : Measurable H) (T : ℝ≥0)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    Measurable (fun ω =>
      if ∀ s : ℝ≥0, s ≤ T → 0 ≤ H ω + X.X s ω
      then ENNReal.ofReal
        (Real.exp (-(q * (T : ℝ))) * W (H ω + X.X T ω))
      else (0 : ℝ≥0∞)) := by
  have hs : MeasurableSet
      {ω : Ω | ∀ s : ℝ≥0, s ≤ T → 0 ≤ H ω + X.X s ω} :=
    chat04_random_reserve_closed_survival_measurable X H hH T
  have ht : Measurable (fun ω => H ω + X.X T ω) :=
    hH.add ((X.adapted T).mono (𝓕.le T) le_rfl)
  have hpay : Measurable (fun ω =>
      ENNReal.ofReal
        (Real.exp (-(q * (T : ℝ))) * W (H ω + X.X T ω))) :=
    ENNReal.measurable_ofReal.comp
      (measurable_const.mul
        ((chat04_scaleFunction_measurable_of_punctured_continuity X q W hW).comp ht))
  exact hpay.ite hs measurable_const
