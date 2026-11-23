-- Prove2me | solution 1 for DedekindZeta.Theta.integral_comp_continuousLinearEquiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:16:50.218904+00:00
-- url     : https://prove2.me/submissions/e65f7d22-d7d7-4aba-98f9-c55097a58909

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.mixedGaussianSchwartz_apply

set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
open MeasureTheory
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
namespace DedekindZeta.Theta
theorem _root_.solution {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (A : V ≃L[ℝ] V) (g : V → F) :
    ∫ v, g (A v) = |(LinearMap.det (A : V →ₗ[ℝ] V))⁻¹| • ∫ u, g u := by
  by_cases hF : CompleteSpace F
  · have hdet : LinearMap.det (A : V →ₗ[ℝ] V) ≠ 0 := by
      have : IsUnit (LinearMap.det (A.toLinearEquiv : V →ₗ[ℝ] V)) :=
        LinearEquiv.isUnit_det' A.toLinearEquiv
      simpa using this.ne_zero
    have hmap : Measure.map A (volume : Measure V)
        = ENNReal.ofReal |(LinearMap.det (A : V →ₗ[ℝ] V))⁻¹| • (volume : Measure V) := by
      simpa using Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure V) hdet
    calc
      ∫ v, g (A v)
          = ∫ u, g u ∂(Measure.map A (volume : Measure V)) :=
            (integral_map_equiv A.toHomeomorph.toMeasurableEquiv g).symm
      _ = |(LinearMap.det (A : V →ₗ[ℝ] V))⁻¹| • ∫ u, g u := by
            rw [hmap, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _)]
  · simp [integral, hF]
end DedekindZeta.Theta
