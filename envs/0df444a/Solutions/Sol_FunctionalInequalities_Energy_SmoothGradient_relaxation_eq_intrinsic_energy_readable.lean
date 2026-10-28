-- Prove2me | solution 1 for FunctionalInequalities.Energy.SmoothGradient.relaxation_eq_intrinsic_energy_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:03:32.562287+00:00
-- url     : https://prove2.me/submissions/14fd8840-5afd-4c72-a300-41b4b9ff4e5b

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Comparison
import Theorems.Thm_FunctionalInequalities_Energy_Euclidean_toAmbientL2_toIntrinsicL2_readable
import Theorems.Thm_FunctionalInequalities_Energy_SmoothGradient_Test_exists_ambient_extension_readable

section
section
variable {X : Type*}
/-- Extended energy functionals are equal when all of their values are equal. -/
@[ext]
theorem FunctionalInequalities.Energy.Functional.ext {left right : Functional X} (h : ∀ x, left x = right x) : left = right := by
  cases left with
  | mk left =>
    cases right with
    | mk right =>
      congr
      funext x
      exact h x
end
end

section
noncomputable section
open Filter Topology
section
universe u v
section
variable {X : Type u} [TopologicalSpace X] (P : FunctionalInequalities.Energy.PreEnergy X)
/-- The relaxed energy is the infimum of the `liminf` energies of all approximating sequences. -/
theorem FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_apply (x : X) :
    P.sequentialRelaxation x = ⨅ f : P.ApproximatingSequence x, P.sequenceEnergy f :=
  rfl
/-- Every particular approximating sequence gives an upper bound for the relaxed energy. -/
theorem FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_le_sequenceEnergy {x : X} (f : P.ApproximatingSequence x) :
    P.sequentialRelaxation x ≤ P.sequenceEnergy f :=
  iInf_le _ f
/-- A continuous map with energy-nonincreasing lifts on concrete tests has the same bound
after relaxation. Neither test class needs to be nonempty or densely realized.

Each source test must have one target test realizing its image exactly. For comparison by
approximating sequences in a common pseudometric space, see
`PreEnergy.sequentialRelaxation_le_of_recovery_sequences` in
`FunctionalInequalities.Energy.Relaxation.LowerSemicontinuous`. The present result only needs
topological ambient spaces and also allows a map between different spaces.
-/
theorem FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_comp_le {Y : Type*} [TopologicalSpace Y]
    (Q : PreEnergy Y) (T : X → Y) (hT : Continuous T)
    (h : ∀ f : P.Test, ∃ g : Q.Test,
      Q.toAmbient g = T (P.toAmbient f) ∧ Q.energy g ≤ P.energy f) (x : X) :
    Q.sequentialRelaxation (T x) ≤ P.sequentialRelaxation x := by
  rw [P.sequentialRelaxation_apply]
  refine le_iInf fun s ↦ ?_
  choose g hreal henergy using fun n ↦ h (s.1 n)
  have hconv : Tendsto (fun n ↦ Q.toAmbient (g n)) atTop (𝓝 (T x)) := by
    simpa only [hreal, Function.comp_def] using (hT.tendsto x).comp s.2
  exact (Q.sequentialRelaxation_le_sequenceEnergy ⟨g, hconv⟩).trans
    (liminf_le_liminf (Eventually.of_forall fun n ↦ ENNReal.coe_le_coe.mpr (henergy n)))
end
end
end
end

noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
open scoped ContDiff
open FunctionalInequalities.Energy.Euclidean
universe u
private theorem FunctionalInequalities.Energy.SmoothGradient.pullbackTest_energy_le
    {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y] [MeasurableSpace Y]
    {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y} (f : Test ν)
    (φ : X → Y) (hφ : ContDiff ℝ ∞ φ) (hlip : LipschitzWith 1 φ)
    (hmp : MeasurePreserving φ (μ : Measure X) (ν : Measure Y)) :
    (FunctionalInequalities.Energy.SmoothGradient.pullbackTest f φ hφ hlip hmp).energy ≤ f.energy := by
  apply NNReal.coe_le_coe.mp
  calc
    _ ≤ ∫ x, ‖gradient f (φ x)‖ ^ 2 ∂(μ : Measure X) := by
      apply integral_mono (FunctionalInequalities.Energy.SmoothGradient.pullbackTest f φ hφ hlip hmp).gradient_sq_integrable
        (hmp.integrable_comp_of_integrable f.gradient_sq_integrable)
      intro x
      exact pow_le_pow_left₀ (norm_nonneg _) (FunctionalInequalities.Energy.SmoothGradient.norm_gradient_comp_le f.contDiff hφ hlip x) 2
    _ = _ := by
      have h := integral_map hmp.measurable.aemeasurable
        (hmp.map_eq.symm ▸ f.gradient_sq_integrable.aestronglyMeasurable)
      simpa only [hmp.map_eq, Test.coe_energy] using h.symm
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
  (μ : MeasureTheory.ProbabilityMeasure E)
section
/-- Restriction has the expected `L²` realization and does not increase raw energy.
Source: the tangential-gradient projection argument in the local Blueprint comparison. -/
theorem FunctionalInequalities.Energy.SmoothGradient.Test.exists_intrinsic_restriction (f : Energy.SmoothGradient.Test μ) :
    ∃ g : Energy.SmoothGradient.Test (Probability.intrinsicMeasure μ),
      (∀ v, g v = f (Probability.reconstruct μ v)) ∧
      g.toL2 = toIntrinsicL2 μ f.toL2 ∧ g.energy ≤ f.energy := by
  let φ := Probability.reconstruct μ
  have hφ : ContDiff ℝ ∞ φ := φ.toContinuousAffineMap.contDiff
  let g := FunctionalInequalities.Energy.SmoothGradient.pullbackTest f φ hφ φ.isometry.lipschitz
    (Probability.measurePreserving_reconstruct μ)
  exact ⟨g, fun _ ↦ rfl, rfl,
    pullbackTest_energy_le f φ hφ φ.isometry.lipschitz
      (Probability.measurePreserving_reconstruct μ)⟩
end
/-- The two extended energies agree on the original `L²(μ)` space, including at infinity.
Source: Blueprint `thm:ambient-intrinsic-relaxation-equality`, using the preceding test maps. -/
theorem solution :
    FunctionalInequalities.Energy.SmoothGradient.relaxation μ = FunctionalInequalities.Energy.SmoothGradient.Intrinsic.energy μ := by
  apply FunctionalInequalities.Energy.Functional.ext
  intro f
  change (FunctionalInequalities.Energy.SmoothGradient.preEnergy μ).sequentialRelaxation f =
    (FunctionalInequalities.Energy.SmoothGradient.preEnergy (FunctionalInequalities.Probability.intrinsicMeasure μ)).sequentialRelaxation
      (FunctionalInequalities.Energy.Euclidean.toIntrinsicL2 μ f)
  apply le_antisymm
  · have h := (FunctionalInequalities.Energy.SmoothGradient.preEnergy (FunctionalInequalities.Probability.intrinsicMeasure μ)).sequentialRelaxation_comp_le
      (FunctionalInequalities.Energy.SmoothGradient.preEnergy μ) (FunctionalInequalities.Energy.Euclidean.toAmbientL2 μ) (FunctionalInequalities.Energy.Euclidean.toAmbientL2 μ).continuous
      (fun g ↦ by
        obtain ⟨t, _, ht, he⟩ := g.exists_ambient_extension_readable μ
        refine ⟨t, ?_, he.le⟩
        change t.toL2 = FunctionalInequalities.Energy.Euclidean.toAmbientL2 μ g.toL2
        rw [← ht, FunctionalInequalities.Energy.Euclidean.toAmbientL2_toIntrinsicL2_readable]) (FunctionalInequalities.Energy.Euclidean.toIntrinsicL2 μ f)
    simpa only [FunctionalInequalities.Energy.Euclidean.toAmbientL2_toIntrinsicL2_readable] using h
  · exact (FunctionalInequalities.Energy.SmoothGradient.preEnergy μ).sequentialRelaxation_comp_le
      (FunctionalInequalities.Energy.SmoothGradient.preEnergy (FunctionalInequalities.Probability.intrinsicMeasure μ))
      (FunctionalInequalities.Energy.Euclidean.toIntrinsicL2 μ) (FunctionalInequalities.Energy.Euclidean.toIntrinsicL2 μ).continuous
      (fun t ↦ by
        obtain ⟨g, _, hg, he⟩ := t.exists_intrinsic_restriction μ
        exact ⟨g, hg, he⟩) f
