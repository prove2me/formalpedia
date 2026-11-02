-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_06_original_rightcont_stopping_nnreal_real_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T22:57:16.788744+00:00
-- url     : https://prove2.me/submissions/a87e0f12-1536-4426-9239-1c4b2ab58707

import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Every finite original right-continuous stopping clock is an ordinary
measurable real-valued random variable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    Measurable (fun ω : Ω => (τ ω : ℝ)) := by
  have hτENN : Measurable (fun ω : Ω => (τ ω : WithTop ℝ≥0)) :=
    hτ.measurable'
  have hτNN : Measurable τ :=
    measurable_coe_nnreal_ennreal_iff.mp hτENN
  exact hτNN.coe_nnreal_real
