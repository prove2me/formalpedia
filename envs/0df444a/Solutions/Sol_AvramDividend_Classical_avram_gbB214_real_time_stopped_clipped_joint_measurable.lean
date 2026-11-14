-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB214_real_time_stopped_clipped_joint_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:16:00.402234+00:00
-- url     : https://prove2.me/submissions/0596f0dd-3e03-4ef1-850f-6e3af09db7e9

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

/-- The original-type clipped physical-time stopped coefficient is jointly measurable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (Y : ℝ≥0 → Ω → ℝ)
    (hY : Measurable (fun z : ℝ≥0 × Ω => Y z.1 z.2))
    (ρ : Ω → ℝ≥0) (hρ : Measurable ρ)
    (g : ℝ → ℝ) (hg : Measurable g) (q : ℝ) :
    Measurable (fun z : ℝ × Ω =>
      if z.1 < (ρ z.2 : ℝ) then
        Real.exp (-(q * z.1)) * g (Y (Real.toNNReal z.1) z.2)
      else 0) := by
  have hρr : Measurable (fun z : ℝ × Ω => (ρ z.2 : ℝ)) :=
    (NNReal.continuous_coe.measurable.comp hρ).comp measurable_snd
  have ht : Measurable (fun z : ℝ × Ω => Real.toNNReal z.1) :=
    continuous_real_toNNReal.measurable.comp measurable_fst
  have hYr : Measurable (fun z : ℝ × Ω =>
      Y (Real.toNNReal z.1) z.2) :=
    hY.comp (ht.prodMk measurable_snd)
  have hpre : MeasurableSet {z : ℝ × Ω | z.1 < (ρ z.2 : ℝ)} :=
    measurableSet_lt measurable_fst hρr
  have hexp : Measurable (fun z : ℝ × Ω =>
      Real.exp (-(q * z.1))) := by fun_prop
  have hprod : Measurable (fun z : ℝ × Ω =>
      Real.exp (-(q * z.1)) * g (Y (Real.toNNReal z.1) z.2)) :=
    hexp.mul (hg.comp hYr)
  exact hprod.ite hpre measurable_const

