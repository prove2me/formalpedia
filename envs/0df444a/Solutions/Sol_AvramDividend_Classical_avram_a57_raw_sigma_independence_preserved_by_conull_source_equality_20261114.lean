-- Prove2me | solution 1 for AvramDividend.Classical.avram_a57_raw_sigma_independence_preserved_by_conull_source_equality_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:31:42.391538+00:00
-- url     : https://prove2.me/submissions/53d33294-ae62-4e4a-9e1d-4c2bdc47efdd

import Mathlib.Probability.Independence.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

/-- Independence from a fixed raw sigma algebra is invariant under source almost-everywhere replacement of a real random variable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (𝓐 : MeasurableSpace Ω)
    (f g : Ω → ℝ)
    (hEq : f =ᵐ[P] g)
    (hInd : Indep (MeasurableSpace.comap f inferInstance) 𝓐 P) :
    Indep (MeasurableSpace.comap g inferInstance) 𝓐 P := by
  letI : MeasurableSpace Ω := 𝓐
  have hIndFun : f ⟂ᵢ[P] (id : Ω → Ω) := by
    apply (IndepFun_iff_Indep f (id : Ω → Ω) P).2
    change Indep (MeasurableSpace.comap f inferInstance)
      (MeasurableSpace.comap (id : Ω → Ω) 𝓐) P
    simpa only [MeasurableSpace.comap_id] using hInd
  have hEqFun : f ⟂ᵢ[P] (id : Ω → Ω) :=
    hIndFun
  have hG : g ⟂ᵢ[P] (id : Ω → Ω) :=
    hEqFun.congr hEq Filter.EventuallyEq.rfl
  have hSigma := (IndepFun_iff_Indep g (id : Ω → Ω) P).1 hG
  change Indep (MeasurableSpace.comap g inferInstance) 𝓐 P
  simpa only [MeasurableSpace.comap_id] using hSigma
