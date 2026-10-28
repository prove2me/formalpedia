-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.cumulant_map_linearIsometryEquiv_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:25:08.088837+00:00
-- url     : https://prove2.me/submissions/aab8f6cc-8bca-4f43-bd8d-f08f738036b6

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace ContDiff
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- Iterated derivatives of a composition with a continuous linear equivalence. -/
private theorem FunctionalInequalities.Analysis.BakryEmery.equiv_iteratedFDeriv_univ {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (g : G ≃L[ℝ] E) (f : E → F) (x : G) (i : ℕ) :
    iteratedFDeriv ℝ i (f ∘ g) x =
      (iteratedFDeriv ℝ i f (g x)).compContinuousLinearMap
        (fun _ => (g : G →L[ℝ] E)) := by
  simpa only [Set.preimage_univ, iteratedFDerivWithin_univ] using
    g.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ
      (Set.mem_univ (g x)) i
section InnerProduct
variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- **Cumulants along a linear isometry**: `κ^{φ_*ν}_k(φ u₁, …, φ u_k) = κ^ν_k(u₁, …, u_k)` for
every measure `ν`, since `Λ_{φ_*ν} = Λ_ν ∘ φ⁻¹` pointwise. -/
theorem solution [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (φ : E ≃ₗᵢ[ℝ] F) (ν : Measure E) (k : ℕ) (u : Fin k → E) :
    FunctionalInequalities.Analysis.BakryEmery.cumulant (ν.map φ) k (fun i => φ (u i)) = FunctionalInequalities.Analysis.BakryEmery.cumulant ν k u := by
    have hlog :
        FunctionalInequalities.Analysis.BakryEmery.logLaplace (ν.map φ) = FunctionalInequalities.Analysis.BakryEmery.logLaplace ν ∘ (φ.symm : F → E) := by
      funext z
      simp only [FunctionalInequalities.Analysis.BakryEmery.logLaplace, Function.comp_apply]
      let hcont : Continuous (fun y : F => Real.exp ⟪z, y⟫) :=
        Real.continuous_exp.comp (continuous_const.inner continuous_id)
      have hz :
          AEStronglyMeasurable (fun y : F => Real.exp ⟪z, y⟫) (ν.map φ) :=
        hcont.aestronglyMeasurable
      have hmap :
          (∫ y : F, Real.exp ⟪z, y⟫ ∂(ν.map φ)) =
            ∫ x : E, Real.exp ⟪z, φ x⟫ ∂ν := by
        rw [integral_map φ.continuous.measurable.aemeasurable hz]
      have hinner :
          (∫ x : E, Real.exp ⟪z, φ x⟫ ∂ν) =
            ∫ x : E, Real.exp ⟪φ.symm z, x⟫ ∂ν := by
        apply integral_congr_ae
        filter_upwards [] with x
        have hx : ⟪z, φ x⟫ = ⟪φ.symm z, x⟫ := by
          simpa using (φ.symm.inner_map_map z (φ x)).symm
        rw [hx]
      rw [hmap, hinner]

    change
      (iteratedFDeriv ℝ k (FunctionalInequalities.Analysis.BakryEmery.logLaplace (ν.map φ)) 0)
          (fun i => φ (u i)) =
        (iteratedFDeriv ℝ k (FunctionalInequalities.Analysis.BakryEmery.logLaplace ν) 0) u
    rw [hlog]
    have hderiv :
        iteratedFDeriv ℝ k (FunctionalInequalities.Analysis.BakryEmery.logLaplace ν ∘ (φ.symm : F → E)) 0 =
          (iteratedFDeriv ℝ k (FunctionalInequalities.Analysis.BakryEmery.logLaplace ν) 0).compContinuousLinearMap
            (fun _ => (φ.symm.toContinuousLinearEquiv : F →L[ℝ] E)) := by
      simpa using
        (FunctionalInequalities.Analysis.BakryEmery.equiv_iteratedFDeriv_univ
          (g := φ.symm.toContinuousLinearEquiv) (f := FunctionalInequalities.Analysis.BakryEmery.logLaplace ν)
          (x := (0 : F)) (i := k))
    rw [hderiv]
    simp [ContinuousMultilinearMap.compContinuousLinearMap_apply]
