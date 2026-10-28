-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.exists_smoothGradient_localDensity_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:41:51.550901+00:00
-- url     : https://prove2.me/submissions/fe1e3449-9c27-4f6a-bb64-664b179c0d45

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Energy

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open FunctionalInequalities.Energy FunctionalInequalities.Energy.Euclidean FunctionalInequalities.Probability
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
section FullDimensional
variable {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure]
omit [CompleteSpace V] in
/-- A full-dimensional log-concave law admits the local-density package used by the smooth-core
comparison. -/
theorem solution (hν : FunctionalInequalities.KLS.LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) :
    Nonempty (FunctionalInequalities.Energy.SmoothGradient.LocalDensity ν m) := by
  obtain ⟨ρ, hρ⟩ := hν.exists_isBorellDensity_of_interior_support_nonempty m hi
    (hν.absolutelyContinuous_haar m hi)
  refine ⟨{
    Ω := interior (ν : Measure V).support
    isOpen := isOpen_interior
    ρ := ρ
    measurable := hρ.measurable
    compl_null := ?_
    restrict_eq := ?_
    pos := ?_
    inv_locallyBounded := ?_ }⟩
  · have hsub : (interior (ν : Measure V).support)ᶜ ⊆
        (ν : Measure V).supportᶜ ∪ frontier (ν : Measure V).support := by
      intro x hx
      by_cases hs : x ∈ (ν : Measure V).support
      · exact Or.inr ⟨subset_closure hs, hx⟩
      · exact Or.inl hs
    exact measure_mono_null hsub
      (measure_union_null Measure.measure_compl_support (hν.frontier_support_eq_zero hi))
  · rw [← hρ.withDensity_eq,
      MeasureTheory.restrict_withDensity isOpen_interior.measurableSet]
  · exact Filter.Eventually.of_forall fun x hx ↦ hρ.pos_of_mem_interior_support hx
  · intro K hK hKΩ
    obtain ⟨a, _b, ha, hab⟩ := hρ.exists_bounds_of_isCompact hK hKΩ
    refine ⟨a⁻¹, Filter.Eventually.of_forall fun x hx ↦ ?_⟩
    simpa only [one_div] using one_div_le_one_div_of_le ha (hab x hx).1
