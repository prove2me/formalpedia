-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_indep_source_sigma_comap_ae_congr_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:45:48.284328+00:00
-- url     : https://prove2.me/submissions/951d0555-eea8-46c1-8b0c-a302a58b84ab

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

/-- Independence of a Borel source observable from any original sub-sigma-algebra transfers across a.e. equality. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (H : MeasurableSpace Ω)
    (D E : Ω → ℝ)
    (hInd : Indep (MeasurableSpace.comap D inferInstance) H P)
    (hEq : D =ᵐ[P] E) :
    Indep (MeasurableSpace.comap E inferInstance) H P := by
  letI : MeasurableSpace (ULift.{0} Ω) :=
    MeasurableSpace.comap ULift.down H
  let U : Ω → ULift.{0} Ω := ULift.up
  have hSame : MeasurableSpace.comap U inferInstance = H := by
    change MeasurableSpace.comap U
      (MeasurableSpace.comap ULift.down H) = H
    rw [MeasurableSpace.comap_comp]
    have hComp : ULift.down ∘ U = id := by
      funext ω
      rfl
    rw [hComp, MeasurableSpace.comap_id]
  have hFun : IndepFun D U P := by
    change Indep (MeasurableSpace.comap D inferInstance)
      (MeasurableSpace.comap U inferInstance) P
    simpa only [hSame] using hInd
  have hFun' : IndepFun E U P :=
    hFun.congr hEq Filter.EventuallyEq.rfl
  change Indep (MeasurableSpace.comap E inferInstance)
    (MeasurableSpace.comap U inferInstance) P at hFun'
  simpa only [hSame] using hFun'
