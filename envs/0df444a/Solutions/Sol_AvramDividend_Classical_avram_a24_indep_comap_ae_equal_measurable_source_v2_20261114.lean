-- Prove2me | solution 1 for AvramDividend.Classical.avram_a24_indep_comap_ae_equal_measurable_source_v2_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:12:00.796466+00:00
-- url     : https://prove2.me/submissions/64ec0745-eebe-48a1-821c-c7c02c30260c

import Mathlib.Probability.Independence.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- AE-equal measurable random variables generate the same independence relationships with a source sub-sigma-algebra. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (A : MeasurableSpace Ω) (hA : A ≤ mΩ)
    (f g : Ω → ℝ) (hf : Measurable[mΩ] f) (hg : Measurable[mΩ] g)
    (hEq : f =ᵐ[P] g)
    (hInd : Indep (MeasurableSpace.comap f inferInstance) A P) :
    Indep (MeasurableSpace.comap g inferInstance) A P := by
  letI : MeasurableSpace Ω := mΩ
  apply (indep_iff_forall_indepSet P).2
  intro s t hs ht
  obtain ⟨B, hB, rfl⟩ :=
    (MeasurableSpace.measurableSet_comap).1 hs
  have hSf : MeasurableSet[MeasurableSpace.comap f inferInstance] (f ⁻¹' B) :=
    (MeasurableSpace.measurableSet_comap).2 ⟨B, hB, rfl⟩
  have hIndSet : IndepSet (f ⁻¹' B) t P :=
    hInd.indepSet_of_measurableSet hSf ht
  have hAEset : (g ⁻¹' B) =ᵐ[P] (f ⁻¹' B) := by
    filter_upwards [hEq] with ω hω
    change (g ω ∈ B) = (f ω ∈ B)
    rw [hω]
  have hAEint : (Set.inter (g ⁻¹' B) t) =ᵐ[P] (Set.inter (f ⁻¹' B) t) := by
    filter_upwards [hEq] with ω hω
    change (g ω ∈ B ∧ ω ∈ t) = (f ω ∈ B ∧ ω ∈ t)
    rw [hω]
  apply (indepSet_iff_measure_inter_eq_mul
      (hB.preimage hg) (hA t ht) (μ := P)).2
  calc
    P (Set.inter (g ⁻¹' B) t) = P (Set.inter (f ⁻¹' B) t) := measure_congr hAEint
    _ = P (f ⁻¹' B) * P t := hIndSet.measure_inter_eq_mul
    _ = P (g ⁻¹' B) * P t := by rw [measure_congr hAEset]
