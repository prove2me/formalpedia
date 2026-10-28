-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_intervalIntegrable_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:15:30.064991+00:00
-- url     : https://prove2.me/submissions/4c6b2d07-def5-494c-98bb-4b1f25deb5d7

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_scaleFunction_measurable_of_punctured_continuity
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal

/-- A nonnegative monotone scale function is integrable on each finite positive interval. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable W volume a b := by
  have hmeas : Measurable W :=
    chat04_scaleFunction_measurable_of_punctured_continuity X q W hW
  have hsubset : Ioc a b ⊆ Icc a b := by
    intro z hz
    exact ⟨le_of_lt hz.1, hz.2⟩
  have hfinite : volume (Ioc a b) < ⊤ :=
    (measure_mono hsubset).trans_lt (isCompact_Icc.measure_lt_top)
  have hsm : AEStronglyMeasurable W (volume.restrict (Ioc a b)) :=
    hmeas.aestronglyMeasurable
  have hbound : ∀ᵐ z : ℝ ∂(volume.restrict (Ioc a b)), ‖W z‖ ≤ W b := by
    filter_upwards [(ae_restrict_mem (μ := volume) measurableSet_Ioc)] with z hz
    have hz0 : 0 ≤ z := le_trans ha (le_of_lt hz.1)
    have hb0 : 0 ≤ b := le_trans ha hab
    rw [Real.norm_eq_abs, abs_of_nonneg (hW.2.1 z hz0)]
    exact hW.2.2.2.1 (mem_Ici.mpr hz0) (mem_Ici.mpr hb0) hz.2
  have hint : IntegrableOn W (Ioc a b) volume :=
    IntegrableOn.of_bound hfinite hsm (W b) hbound
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 hint
