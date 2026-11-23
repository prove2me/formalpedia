-- Prove2me | solution 1 for DedekindZeta.Theta.fourier_comp_continuousLinearEquiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:19:14.585296+00:00
-- url     : https://prove2.me/submissions/c3a709d2-82ab-49ca-bf69-909413490264

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_integral_comp_continuousLinearEquiv
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
theorem _root_.solution (A : V ≃L[ℝ] V) (f : V → ℂ) (w : V) :
    𝓕 (fun v => f (A v)) w
      = ((|(LinearMap.det (A : V →ₗ[ℝ] V))|⁻¹ : ℝ) : ℂ) •
          𝓕 f (ContinuousLinearMap.adjoint (A.symm : V →L[ℝ] V) w) := by
  -- Set `g u := 𝐞(-⟪A.symm u, w⟫) • f u`; then the Fourier integrand for `f ∘ A`
  -- equals `g ∘ A` pointwise, because `A.symm (A v) = v`.
  set g : V → ℂ := fun u => (Real.fourierChar (-⟪u, ContinuousLinearMap.adjoint
    (A.symm : V →L[ℝ] V) w⟫ : ℝ) : ℂ) • f u with hg
  have key : ∀ v : V, (Real.fourierChar (-⟪v, w⟫ : ℝ) : ℂ) • f (A v) = g (A v) := by
    intro v
    have hadj : (⟪(A v), ContinuousLinearMap.adjoint (A.symm : V →L[ℝ] V) w⟫ : ℝ)
        = ⟪v, w⟫ := by
      rw [ContinuousLinearMap.adjoint_inner_right]
      simp
    simp only [hg]
    rw [hadj]
  rw [Real.fourier_eq]
  simp only [Circle.smul_def] at key ⊢
  rw [show (∫ v, (Real.fourierChar (-⟪v, w⟫ : ℝ) : ℂ) • f (A v))
        = ∫ v, g (A v) from integral_congr_ae (Filter.Eventually.of_forall key)]
  rw [integral_comp_continuousLinearEquiv A g, Real.fourier_eq]
  simp only [hg, Circle.smul_def]
  rw [Complex.real_smul, smul_eq_mul, abs_inv]
end DedekindZeta.Theta
