-- Prove2me | solution 1 for FunctionalInequalities.Energy.SmoothGradient.Test.exists_ambient_extension_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:44:27.437894+00:00
-- url     : https://prove2.me/submissions/3235cbb3-1f40-4fb0-91de-0a89157d320c

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLSModular_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Comparison

section
noncomputable section
open MeasureTheory
section
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E]
section Coordinates
variable [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
omit [CompleteSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- On the affine support, the retraction is the identity. -/
@[simp]
theorem FunctionalInequalities.Probability.coe_retraction_of_mem (μ : ProbabilityMeasure E) {x : E}
    (hx : x ∈ affineSupport μ) : (retraction μ x : E) = x := by
  classical
  simp [retraction, hx]
omit [CompleteSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- Taking intrinsic coordinates after reconstruction recovers the original coordinates. -/
@[simp]
theorem FunctionalInequalities.Probability.intrinsicMap_reconstruct (μ : ProbabilityMeasure E)
    (v : (affineSupport μ).direction) :
    intrinsicMap μ (reconstruct μ v) = v := by
  have hmem : reconstruct μ v ∈ affineSupport μ :=
    (coordinateEquiv μ v).property
  have hret : retraction μ (reconstruct μ v) = coordinateEquiv μ v := by
    apply Subtype.ext
    exact coe_retraction_of_mem μ hmem
  rw [intrinsicMap, hret]
  exact (coordinateEquiv μ).symm_apply_apply v
end Coordinates
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
omit [CompleteSpace E] [BorelSpace E] in
private theorem FunctionalInequalities.Energy.SmoothGradient.projectionCoordinates_reconstruct (v : (Probability.affineSupport μ).direction) :
    FunctionalInequalities.Energy.SmoothGradient.projectionCoordinates μ (Probability.reconstruct μ v) = v := by
  change (Probability.affineSupport μ).direction.orthogonalProjectionOnto
    ((v : E) + Probability.supportPoint μ - Probability.supportPoint μ) = v
  simp
omit [CompleteSpace E] [BorelSpace E] in
private theorem FunctionalInequalities.Energy.SmoothGradient.contDiff_projectionCoordinates : ContDiff ℝ ∞ (FunctionalInequalities.Energy.SmoothGradient.projectionCoordinates μ) :=
  (Probability.affineSupport μ).direction.orthogonalProjectionOnto.contDiff.comp
    (contDiff_id.sub contDiff_const)
omit [CompleteSpace E] [BorelSpace E] in
private theorem FunctionalInequalities.Energy.SmoothGradient.lipschitz_projectionCoordinates : LipschitzWith 1 (FunctionalInequalities.Energy.SmoothGradient.projectionCoordinates μ) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  simpa only [FunctionalInequalities.Energy.SmoothGradient.projectionCoordinates, dist_eq_norm, ← map_sub, sub_sub_sub_cancel_right,
    NNReal.coe_one, one_mul] using
    (Probability.affineSupport μ).direction.norm_orthogonalProjectionOnto_apply_le (x - y)
omit [CompleteSpace E] in
private theorem FunctionalInequalities.Energy.SmoothGradient.measurePreserving_projectionCoordinates :
    MeasurePreserving (FunctionalInequalities.Energy.SmoothGradient.projectionCoordinates μ) (μ : Measure E)
      (Probability.intrinsicMeasure μ : Measure _) := by
  have hae : FunctionalInequalities.Energy.SmoothGradient.projectionCoordinates μ =ᵐ[(μ : Measure E)] Probability.intrinsicMap μ := by
    filter_upwards [Probability.reconstruct_intrinsicMap_ae μ] with x hx
    rw [← hx, projectionCoordinates_reconstruct, Probability.intrinsicMap_reconstruct]
  exact ⟨(contDiff_projectionCoordinates μ).continuous.measurable,
    (Measure.map_congr hae).trans (Probability.measurePreserving_intrinsicMap μ).map_eq⟩
/-- An intrinsic test has a smooth ambient extension with exactly the same raw energy.
Source: extension through orthogonal projection in the local Blueprint comparison. -/
theorem solution
    (g : FunctionalInequalities.Energy.SmoothGradient.Test (FunctionalInequalities.Probability.intrinsicMeasure μ)) :
    ∃ f : FunctionalInequalities.Energy.SmoothGradient.Test μ,
      (∀ v, f (FunctionalInequalities.Probability.reconstruct μ v) = g v) ∧
      FunctionalInequalities.Energy.Euclidean.toIntrinsicL2 μ f.toL2 = g.toL2 ∧ f.energy = g.energy := by
  let f := FunctionalInequalities.Energy.SmoothGradient.pullbackTest g (FunctionalInequalities.Energy.SmoothGradient.projectionCoordinates μ) (FunctionalInequalities.Energy.SmoothGradient.contDiff_projectionCoordinates μ)
    (FunctionalInequalities.Energy.SmoothGradient.lipschitz_projectionCoordinates μ) (FunctionalInequalities.Energy.SmoothGradient.measurePreserving_projectionCoordinates μ)
  have hpoint : ∀ v, f (FunctionalInequalities.Probability.reconstruct μ v) = g v := by
    intro v
    change g (FunctionalInequalities.Energy.SmoothGradient.projectionCoordinates μ (FunctionalInequalities.Probability.reconstruct μ v)) = g v
    rw [FunctionalInequalities.Energy.SmoothGradient.projectionCoordinates_reconstruct]
  obtain ⟨r, hr, hL2, henergy⟩ := f.exists_intrinsic_restriction μ
  have hrg : r = g := by
    have hfun : r.toFun = g.toFun := funext fun v ↦ (hr v).trans (hpoint v)
    cases r
    cases g
    cases hfun
    rfl
  subst r
  exact ⟨f, hpoint, hL2.symm, le_antisymm
    (FunctionalInequalities.Energy.SmoothGradient.pullbackTest_energy_le g (FunctionalInequalities.Energy.SmoothGradient.projectionCoordinates μ) (FunctionalInequalities.Energy.SmoothGradient.contDiff_projectionCoordinates μ)
      (FunctionalInequalities.Energy.SmoothGradient.lipschitz_projectionCoordinates μ) (FunctionalInequalities.Energy.SmoothGradient.measurePreserving_projectionCoordinates μ)) henergy⟩
