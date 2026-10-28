-- Prove2me | solution 1 for FunctionalInequalities.Energy.CovarianceGradient.weightedTest_iff_exists_test_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:41:37.370996+00:00
-- url     : https://prove2.me/submissions/9c3b65c7-6b5e-4013-b357-0b7321fe9dcd

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_WeightedGradient_Basic

noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
open FunctionalInequalities.Energy.Euclidean
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
section Gradient
section Measurability
variable [MeasurableSpace V] [BorelSpace V]
section
/-- The weighted gradient of any function is Borel measurable. -/
theorem FunctionalInequalities.Energy.WeightedGradient.measurable_apply (B : V →L[ℝ] V) (g : V → ℝ) :
    Measurable (apply B g) :=
  B.continuous.measurable.comp (LipschitzApproximation.measurable_gradient g)
end
end Measurability
end Gradient
section Operator
variable [MeasurableSpace V] (ν : MeasureTheory.ProbabilityMeasure V) (B : V →L[ℝ] V)
variable [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {m : MeasureTheory.Measure V} [m.IsAddHaarMeasure]
open FunctionalInequalities.Energy.WeightedGradient
omit [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- With `⟪Σ v, v⟫ = ‖B v‖²`, the covariance density is the squared weighted gradient. -/
theorem FunctionalInequalities.Energy.CovarianceGradient.density_eq_norm_sq
    (hB : ∀ v, inner ℝ (Covariance.operator (ν : Measure V) v) v = ‖B v‖ ^ 2) (g : V → ℝ) :
    density ν g = fun x ↦ ‖apply B g x‖ ^ 2 := by
  funext x
  exact hB _
omit [FiniteDimensional ℝ V] in
/-- With `⟪Σ v, v⟫ = ‖B v‖²`, the covariance tests are exactly the gradient tests. -/
theorem solution
    (hB : ∀ v, inner ℝ (FunctionalInequalities.Covariance.operator (ν : Measure V) v) v = ‖B v‖ ^ 2) (g : V → ℝ) :
    FunctionalInequalities.Energy.WeightedGradient.IsTest ν B g ↔ ∃ f : FunctionalInequalities.Energy.CovarianceGradient.Test ν, f.toFun = g := by
  have hmeas : AEStronglyMeasurable (FunctionalInequalities.Energy.WeightedGradient.apply B g) (ν : Measure V) :=
    (FunctionalInequalities.Energy.WeightedGradient.measurable_apply B g).aestronglyMeasurable
  constructor
  · rintro ⟨hK, h2, hBg⟩
    refine ⟨⟨g, hK, h2, ?_⟩, rfl⟩
    rw [FunctionalInequalities.Energy.CovarianceGradient.density_eq_norm_sq ν B hB]
    exact (memLp_two_iff_integrable_sq_norm hmeas).mp hBg
  · rintro ⟨f, rfl⟩
    refine ⟨f.lipschitz, f.memLp_two, ?_⟩
    rw [memLp_two_iff_integrable_sq_norm hmeas, ← FunctionalInequalities.Energy.CovarianceGradient.density_eq_norm_sq ν B hB]
    exact f.integrable
