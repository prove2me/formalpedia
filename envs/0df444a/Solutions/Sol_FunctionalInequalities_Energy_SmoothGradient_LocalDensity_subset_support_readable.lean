-- Prove2me | solution 1 for FunctionalInequalities.Energy.SmoothGradient.LocalDensity.subset_support_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:44:26.35739+00:00
-- url     : https://prove2.me/submissions/4b266fd4-0822-43f1-807e-70f0999082c8

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_SmoothGradient_Core

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
variable {ν : MeasureTheory.ProbabilityMeasure V} {m : MeasureTheory.Measure V} (D : FunctionalInequalities.Energy.SmoothGradient.LocalDensity ν m)
variable [m.IsAddHaarMeasure]
omit [InnerProductSpace ℝ V] [CompleteSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- Every point of `Ω` lies in the support of the law. -/
theorem solution : D.Ω ⊆ (ν : Measure V).support := by
  intro x hx
  rw [Measure.mem_support_iff_forall]
  intro U hU
  obtain ⟨U', hU'U, hU'o, hxU'⟩ := mem_nhds_iff.mp hU
  set W := U' ∩ D.Ω with hW
  have hWo : IsOpen W := hU'o.inter D.isOpen
  have hWne : W.Nonempty := ⟨x, hxU', hx⟩
  have hWΩ : W ⊆ D.Ω := Set.inter_subset_right
  have hmeasf : Measurable fun y ↦ ENNReal.ofReal (D.ρ y) := D.measurable.ennreal_ofReal
  have hpos : 0 < (ν : Measure V) W := by
    rw [D.measure_eq hWo.measurableSet hWΩ, setLIntegral_pos_iff hmeasf]
    refine lt_of_lt_of_le (hWo.measure_pos m hWne) (measure_mono_ae ?_)
    filter_upwards [D.pos] with y hy hyW
    refine ⟨?_, hyW⟩
    rw [Function.mem_support]
    exact (ENNReal.ofReal_pos.mpr (hy (hWΩ hyW))).ne'
  exact hpos.trans_le (measure_mono (Set.inter_subset_left.trans hU'U))
