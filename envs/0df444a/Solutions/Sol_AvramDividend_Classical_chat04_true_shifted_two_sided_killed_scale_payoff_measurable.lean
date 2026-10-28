-- Prove2me | solution 1 for AvramDividend.Classical.chat04_true_shifted_two_sided_killed_scale_payoff_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:32:41.52474+00:00
-- url     : https://prove2.me/submissions/bd14b894-166e-4a95-bb87-d5a8dcc72624

import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_shifted_two_sided_closed_survival_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_scaleFunction_measurable_of_punctured_continuity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable
open AvramDividend.Classical

/-- Real continuous-time two-sided killing leaves a measurable q-scale payoff. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : Ω → ℝ) (hH : Measurable H) (a : ℝ) (b T t : ℝ≥0)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    Measurable (fun ω : Ω =>
      if ∀ v : ℝ≥0, v ≤ T →
        0 ≤ H ω + (X.X (b + v) ω - X.X b ω) ∧
        H ω + (X.X (b + v) ω - X.X b ω) ≤ a
      then ENNReal.ofReal
        (Real.exp (-(q * (t : ℝ))) *
          W (H ω + (X.X (b + t) ω - X.X b ω)))
      else (0 : ℝ≥0∞)) := by
  have hSurvival :=
    chat04_random_reserve_shifted_two_sided_closed_survival_measurable
      X H hH a b T
  have hXm : ∀ u, Measurable (X.X u) :=
    fun u => (X.adapted u).mono (𝓕.le u) le_rfl
  have hReserve : Measurable
      (fun ω : Ω => H ω + (X.X (b + t) ω - X.X b ω)) :=
    hH.add ((hXm (b + t)).sub (hXm b))
  have hScale : Measurable W :=
    chat04_scaleFunction_measurable_of_punctured_continuity X q W hW
  have hPayoff : Measurable (fun ω : Ω =>
      ENNReal.ofReal
        (Real.exp (-(q * (t : ℝ))) *
          W (H ω + (X.X (b + t) ω - X.X b ω)))) :=
    ENNReal.measurable_ofReal.comp
      (measurable_const.mul (hScale.comp hReserve))
  exact hPayoff.ite hSurvival measurable_const
