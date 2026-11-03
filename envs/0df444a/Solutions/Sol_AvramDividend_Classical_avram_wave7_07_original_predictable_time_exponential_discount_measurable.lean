-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_07_original_predictable_time_exponential_discount_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:44:40.243551+00:00
-- url     : https://prove2.me/submissions/eda54687-5690-4ca6-879a-b2fc610a5104

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The deterministic exponential discount is genuinely measurable on
  the original right-continuous predictable sigma algebra. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ} (q : ℝ) :
    Measurable[𝓕.rightCont.predictable]
      (fun p : ℝ≥0 × Ω => Real.exp (-(q * (p.1 : ℝ)))) := by
  classical
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  have hTime : Measurable (fun p : ℝ≥0 × Ω => p.1) := by
    rw [measurable_iff_comap_le]
    rw [BorelSpace.measurable_eq (α := ℝ≥0),
      borel_eq_generateFrom_Ioi (ℝ≥0),
      MeasurableSpace.comap_generateFrom]
    apply MeasurableSpace.generateFrom_le
    intro t ht
    obtain ⟨s, hs, rfl⟩ := ht
    obtain ⟨u, rfl⟩ := hs
    have hIoi :
        MeasurableSet (Ioi u ×ˢ (Set.univ : Set Ω)) :=
      measurableSet_predictable_Ioi_prod (𝓕 := 𝓕.rightCont)
        (i := u) MeasurableSet.univ
    convert hIoi using 1 <;> ext p <;> simp
  have hCoe : Measurable (fun p : ℝ≥0 × Ω => (p.1 : ℝ)) :=
    NNReal.continuous_coe.measurable.comp hTime
  exact Real.measurable_exp.comp ((measurable_const.mul hCoe).neg)