-- Prove2me | solution 1 for FunctionalInequalities.Analysis.exists_C1_height_generator_defect_bound_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:44:42.142686+00:00
-- url     : https://prove2.me/submissions/54538e92-d58c-43bd-890e-e157cb53c822

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_Weak
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_MongeAmpere
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_WeakHessian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_LipschitzBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_DeterminantDerivative
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Piola
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_Coordinates
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_WeakDerivative_Basic
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.Compact
import Theorems.Thm_FunctionalInequalities_Analysis_ae_hessianMatrix_comp_profile_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_deriv_comp_sub_div_and_deriv_deriv_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_exists_majorant_abs_deriv_deriv_smoothTransition_two_sub_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_integral_profile_inverse_energy_eq_drift_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_inv_mul_intervalIntegral_div_three_cutoff_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_smoothTransition_two_sub_cutoff_408915f

section
noncomputable section
open InnerProductSpace
open scoped ContDiff RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
universe u
section DifferentialTools
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section Gradient
variable [CompleteSpace E]
/-- Chain rule for the gradient: `∇(Φ ∘ g) = Φ'(g) ∇g`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.gradient_comp {Φ : ℝ → ℝ} {g : E → ℝ} {x : E} (hΦ : DifferentiableAt ℝ Φ (g x))
    (hg : DifferentiableAt ℝ g x) :
    gradient (fun y => Φ (g y)) x = deriv Φ (g x) • gradient g x := by
  have hcomp : HasFDerivAt (fun y => Φ (g y)) (deriv Φ (g x) • fderiv ℝ g x) x :=
    hΦ.hasDerivAt.comp_hasFDerivAt x hg.hasFDerivAt
  unfold gradient
  rw [hcomp.fderiv, map_smul]
end Gradient
end DifferentialTools
end
end
end
end
end

section
noncomputable section
open MeasureTheory
open scoped ContDiff RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
/-- A unit normalisation `∫ e^{−φ} = 1` forces integrability of `e^{−φ}`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.integrable_exp_neg_of_integral_eq_one {α : Type*} [MeasurableSpace α] (m : Measure α)
    (φ : α → ℝ) (hnorm : ∫ x, Real.exp (-φ x) ∂m = 1) :
    Integrable (fun x => Real.exp (-φ x)) m := by
  by_contra hh
  rw [integral_undef hh] at hnorm
  norm_num at hnorm
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
end
end
end
end
end

section
open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
noncomputable section HessianEntryBounds
open MeasureTheory
open FunctionalInequalities.Probability.Stein
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section
namespace FunctionalInequalities.Probability.Stein
end FunctionalInequalities.Probability.Stein
open FunctionalInequalities FunctionalInequalities.Probability FunctionalInequalities.Probability.Stein
private lemma FunctionalInequalities.Probability.Stein.n10_hessian {n : ℕ}
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    hessianMatrix u x = FunctionalInequalities.Probability.Stein.n10_matrix (fderiv ℝ (gradient u) x) := by
  let T : EuclideanSpace ℝ (Fin n) ≃L[ℝ]
      StrongDual ℝ (EuclideanSpace ℝ (Fin n)) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).toContinuousLinearEquiv
  have he : fderiv ℝ u = T ∘ gradient u :=
    funext fun y => (T.apply_symm_apply (fderiv ℝ u y)).symm
  have hd :
      fderiv ℝ (fderiv ℝ u) x =
        T.toContinuousLinearMap.comp (fderiv ℝ (gradient u) x) :=
    (congrArg (fun f => fderiv ℝ f x) he).trans T.comp_fderiv
  ext r s
  change
    fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.basisFun (Fin n) ℝ r)
        (EuclideanSpace.basisFun (Fin n) ℝ s) =
      T (fderiv ℝ (gradient u) x (EuclideanSpace.basisFun (Fin n) ℝ r))
        (EuclideanSpace.basisFun (Fin n) ℝ s)
  rw [hd]
  rfl
private lemma FunctionalInequalities.Probability.Stein.n11b_continuous_hessian_entry {n : ℕ} (i j : Fin n) :
    Continuous
      (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) =>
        FunctionalInequalities.Probability.Stein.n10_matrix L i j) := by
  let T : EuclideanSpace ℝ (Fin n) ≃L[ℝ]
      StrongDual ℝ (EuclideanSpace ℝ (Fin n)) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).toContinuousLinearEquiv
  exact
    (T.continuous.comp (continuous_id.clm_apply continuous_const)).clm_apply
      continuous_const
/-- Measurability of the total coordinate Hessian, without smoothness premises. -/
theorem FunctionalInequalities.Probability.Stein.measurable_hessianMatrix_entry {n : ℕ}
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (i j : Fin n) :
    Measurable (fun x => hessianMatrix u x i j) := by
  simpa only [n10_hessian, Function.comp_def] using
    (n11b_continuous_hessian_entry i j).measurable.comp
      (measurable_fderiv ℝ (gradient u))
end
end
end
end HessianEntryBounds
end

noncomputable section
open MeasureTheory Filter Set Metric Matrix
open FunctionalInequalities.Probability.Stein
open scoped ContDiff Topology RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
private theorem FunctionalInequalities.Analysis.integrable_profile_energy_and_integral_le {n : ℕ}
    {u V : EuclideanSpace ℝ (Fin n) → ℝ} {ζ : ℝ → ℝ} {G LF : NNReal}
    (hu : ContDiff ℝ 1 u) (hG : LipschitzWith G (gradient u))
    (hV : ContDiff ℝ 1 V)
    (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
    (hζ : ContDiff ℝ 1 ζ) (hζc : HasCompactSupport (fun x => ζ (u x)))
    (hnorm : ∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 1)
    {D B : ℝ} (hD : 0 ≤ D)
    (hζbound : ∀ x, 0 ≤ ζ (u x) ∧ ζ (u x) ≤ B)
    (hdrift : ∀ x, |(n : ℝ) - fderiv ℝ V (gradient u x) (gradient u x)| ≤ D) :
    Integrable (fun x =>
      -(deriv ζ (u x) * (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j))) * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    (∫ x, -(deriv ζ (u x) * (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j))) * Real.exp (-u x)
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤ D * B := by
  have hp := integral_profile_inverse_energy_eq_drift_408915f hu hG hV hF hdet hζ hζc
  have hc : Continuous (fun x => (n : ℝ) -
      fderiv ℝ V (gradient u x) (gradient u x)) :=
    continuous_const.sub
      (((hV.continuous_fderiv one_ne_zero).comp hG.continuous).clm_apply hG.continuous)
  have hi : Integrable (fun x => ζ (u x) *
      ((n : ℝ) - fderiv ℝ V (gradient u x) (gradient u x)) * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (((hζ.continuous.comp hu.continuous).mul hc).mul
      (Real.continuous_exp.comp hu.continuous.neg)).integrable_of_hasCompactSupport
        hζc.mul_right.mul_right
  have hexp := BakryEmery.integrable_exp_neg_of_integral_eq_one
    (volume : Measure (EuclideanSpace ℝ (Fin n))) u hnorm
  have hpoint (x : EuclideanSpace ℝ (Fin n)) :
      ζ (u x) * ((n : ℝ) - fderiv ℝ V (gradient u x) (gradient u x)) * Real.exp (-u x) ≤
        (D * B) * Real.exp (-u x) := by
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    calc
      _ ≤ ζ (u x) * D := mul_le_mul_of_nonneg_left
        ((le_abs_self _).trans (hdrift x)) (hζbound x).1
      _ ≤ B * D := mul_le_mul_of_nonneg_right (hζbound x).2 hD
      _ = _ := mul_comm _ _
  refine ⟨hp.1.neg.congr (Filter.Eventually.of_forall fun x => by
    change -(_ * _) = -_ * _
    ring), ?_⟩
  calc
    _ = _ := hp.2
    _ ≤ ∫ x, (D * B) * Real.exp (-u x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) :=
      integral_mono hi (hexp.const_mul (D * B)) hpoint
    _ = D * B := by rw [integral_const_mul, hnorm, mul_one]
private theorem FunctionalInequalities.Analysis.hasCompactSupport_comp_of_isCompact_sublevel {E : Type*} [TopologicalSpace E] {φ : E → ℝ} {g : ℝ → ℝ} {T : ℝ}
    (hφ : Continuous φ) (hsub : IsCompact {y | φ y ≤ T}) (hg : ∀ s, T ≤ s → g s = 0) :
    HasCompactSupport (fun x => g (φ x)) := by
    refine HasCompactSupport.intro' hsub (isClosed_le hφ continuous_const) ?_
    intro x hx
    have hx' : ¬ φ x ≤ T := hx
    exact hg (φ x) (le_of_lt (lt_of_not_ge hx'))
private theorem FunctionalInequalities.Analysis.shifted_inv_mul_intervalIntegral_div_three_cutoff {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
    (hw0 : ∀ t, 0 ≤ w t) (hws : ∀ t, t ≤ 0 ∨ 3 ≤ t → w t = 0) {R : ℝ} (hR : 0 < R) (c : ℝ) :
    ContDiff ℝ ∞ (fun s => R⁻¹ * ∫ t in (s - c) / R..3, w t) ∧
      (∀ s, deriv (fun s => R⁻¹ * ∫ t in (s - c) / R..3, w t) s = -((R ^ 2)⁻¹ * w ((s - c) / R))) ∧
      (∀ s, |R⁻¹ * ∫ t in (s - c) / R..3, w t| ≤ R⁻¹ * ∫ t in (0 : ℝ)..3, w t) ∧
      (∀ s, c + 3 * R ≤ s → R⁻¹ * ∫ t in (s - c) / R..3, w t = 0) := by
    obtain ⟨hq, hqd, hq0, hqBound, hqZero⟩ :=
      inv_mul_intervalIntegral_div_three_cutoff_408915f hw hw0 hws hR
    let q : ℝ → ℝ := fun t => R⁻¹ * ∫ u in t / R..3, w u
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact hq.comp (contDiff_id.sub contDiff_const)
    · intro s
      have hshift :
          deriv (fun t => q (t - c)) s = deriv q (s - c) := by
        simpa only [div_one, inv_one, one_mul] using
          (deriv_comp_sub_div_and_deriv_deriv_408915f q c 1 s).1
      calc
        deriv (fun t => R⁻¹ * ∫ u in (t - c) / R..3, w u) s =
            deriv q (s - c) := hshift
        _ = -((R ^ 2)⁻¹ * w ((s - c) / R)) := hqd (s - c)
    · intro s
      rw [abs_of_nonneg (hq0 (s - c))]
      exact hqBound (s - c)
    · intro s hs
      exact hqZero (s - c) (by linarith)
private theorem FunctionalInequalities.Analysis.integrable_majorant_inverse_energy_and_integral_le {n : ℕ}
    {u V : EuclideanSpace ℝ (Fin n) → ℝ} {G LF : NNReal}
    (hu : ContDiff ℝ 1 u) (hG : LipschitzWith G (gradient u)) (hV : ContDiff ℝ 1 V)
    (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
    (hnorm : ∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 1)
    (hsub : ∀ t : ℝ, IsCompact {x | u x ≤ t}) {D : ℝ} (hD : 0 ≤ D)
    (hdrift : ∀ x, |(n : ℝ) - fderiv ℝ V (gradient u x) (gradient u x)| ≤ D)
    {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (hw0 : ∀ t, 0 ≤ w t)
    (hws : ∀ t, t ≤ 0 ∨ 3 ≤ t → w t = 0) {R : ℝ} (hR : 0 < R) (c : ℝ) :
    Integrable (fun x => (R ^ 2)⁻¹ * w ((u x - c) / R) *
      (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    (∫ x, (R ^ 2)⁻¹ * w ((u x - c) / R) *
      (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x)
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
        D * (R⁻¹ * ∫ t in (0 : ℝ)..3, w t) := by
  let ζ : ℝ → ℝ := fun s => R⁻¹ * ∫ t in (s - c) / R..3, w t
  obtain ⟨hζ, hζd, hζbound, hζzero⟩ :=
    shifted_inv_mul_intervalIntegral_div_three_cutoff hw hw0 hws hR c
  have hζc : HasCompactSupport (fun x => ζ (u x)) :=
    hasCompactSupport_comp_of_isCompact_sublevel hu.continuous (hsub (c + 3 * R)) hζzero
  obtain ⟨_hq, _hqd, hq0, _hqb, _hqz⟩ :=
    inv_mul_intervalIntegral_div_three_cutoff_408915f hw hw0 hws hR
  have hp := integrable_profile_energy_and_integral_le hu hG hV hF hdet
    (hζ.of_le (WithTop.coe_le_coe.mpr le_top)) hζc hnorm hD
    (fun x => ⟨hq0 (u x - c), (le_abs_self _).trans (hζbound (u x))⟩) hdrift
  have heq (x : EuclideanSpace ℝ (Fin n)) :
      -(deriv ζ (u x) * (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j))) * Real.exp (-u x) =
      (R ^ 2)⁻¹ * w ((u x - c) / R) *
        (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
          fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) *
          fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x) := by
    rw [show deriv ζ (u x) = -((R ^ 2)⁻¹ * w ((u x - c) / R)) from hζd (u x)]
    ring
  refine ⟨hp.1.congr (Filter.Eventually.of_forall heq), ?_⟩
  exact (integral_congr_ae (Filter.Eventually.of_forall fun x => (heq x).symm)).le.trans hp.2
private theorem FunctionalInequalities.Analysis.trace_mul_of_profile_entries {n : ℕ}
    (R H K : Matrix (Fin n) (Fin n) ℝ) (α β : ℝ) (v : Fin n → ℝ)
    (hK : ∀ i j, K i j = α * H i j + β * v i * v j) :
    (R * K).trace = α * (R * H).trace +
      β * (∑ i : Fin n, ∑ j : Fin n, R i j * v i * v j) := by
  have hentry (i j : Fin n) : R i j * K j i =
      α * (R i j * H j i) + β * (R i j * v i * v j) := by
    rw [hK j i]
    ring
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, hentry,
    Finset.sum_add_distrib, ← Finset.mul_sum]
private theorem FunctionalInequalities.Analysis.ae_inverse_hessian_generator_comp_profile {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {ζ : ℝ → ℝ} {G : NNReal}
    (hu : ContDiff ℝ 1 u) (hG : LipschitzWith G (gradient u))
    (hζ : ContDiff ℝ 2 ζ)
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det ≠ 0)
    (V : EuclideanSpace ℝ (Fin n) → ℝ) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ((hessianMatrix u x)⁻¹ * hessianMatrix (fun y => ζ (u y)) x).trace -
          fderiv ℝ V (gradient u x) (gradient (fun y => ζ (u y)) x) =
        deriv ζ (u x) * ((n : ℝ) - fderiv ℝ V (gradient u x) (gradient u x)) +
          deriv (deriv ζ) (u x) *
            (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
              fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) *
              fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j)) := by
  filter_upwards [ae_hessianMatrix_comp_profile_408915f hu hG hζ, hdet] with x hc hd
  have htrace := trace_mul_of_profile_entries (hessianMatrix u x)⁻¹
    (hessianMatrix u x) (hessianMatrix (fun y => ζ (u y)) x)
    (deriv ζ (u x)) (deriv (deriv ζ) (u x))
    (fun i => fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i)) hc
  have hRH : (hessianMatrix u x)⁻¹ * hessianMatrix u x = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hd)
  have hgrad : gradient (fun y => ζ (u y)) x = deriv ζ (u x) • gradient u x :=
    BakryEmery.gradient_comp ((hζ.differentiable (by norm_num)).differentiableAt)
      ((hu.differentiable one_ne_zero).differentiableAt)
  rw [htrace, hRH, hgrad, map_smul]
  simp only [Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
  ring
private theorem FunctionalInequalities.Analysis.sum_inverse_quadratic_nonneg_of_posDef {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (v : Fin n → ℝ) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n, A⁻¹ i j * v i * v j := by
  calc
    0 ≤ star v ⬝ᵥ (A⁻¹ *ᵥ v) := hA.inv.posSemidef.dotProduct_mulVec_nonneg v
    _ = _ := by
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
private theorem FunctionalInequalities.Analysis.measurable_inverse_hessianMatrix_entry_total {n : ℕ}
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (i j : Fin n) :
    Measurable (fun x => (hessianMatrix u x)⁻¹ i j) := by
  classical
  let : MeasurableSpace (Matrix (Fin n) (Fin n) ℝ) :=
    inferInstanceAs (MeasurableSpace (Fin n → Fin n → ℝ))
  let : BorelSpace (Matrix (Fin n) (Fin n) ℝ) :=
    inferInstanceAs (BorelSpace (Fin n → Fin n → ℝ))
  have hH : Measurable (fun x => hessianMatrix u x) :=
    measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun b =>
      measurable_hessianMatrix_entry u a b
  have hdet : Measurable (fun x => (hessianMatrix u x).det) :=
    (show Continuous (fun A : Matrix (Fin n) (Fin n) ℝ => A.det) from
      continuous_id.matrix_det).measurable.comp hH
  have hadj : Measurable (fun x => (hessianMatrix u x).adjugate i j) :=
    ((show Continuous (fun A : Matrix (Fin n) (Fin n) ℝ => A.adjugate) from
      continuous_id.matrix_adjugate).matrix_elem i j).measurable.comp hH
  simpa only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul] using
    hdet.fun_inv.fun_mul hadj
private theorem FunctionalInequalities.Analysis.measurable_inverse_hessian_generator_of_contDiff_one {n : ℕ}
    {u V f : EuclideanSpace ℝ (Fin n) → ℝ} {G : NNReal}
    (hG : LipschitzWith G (gradient u)) (hV : ContDiff ℝ 1 V) (hf : ContDiff ℝ 1 f) :
    Measurable (fun x => ((hessianMatrix u x)⁻¹ * hessianMatrix f x).trace -
      fderiv ℝ V (gradient u x) (gradient f x)) := by
  classical
  have hsum := Finset.measurable_fun_sum Finset.univ fun i _ =>
    Finset.measurable_fun_sum Finset.univ fun j _ =>
      (measurable_inverse_hessianMatrix_entry_total u i j).fun_mul
        (measurable_hessianMatrix_entry f j i)
  have htrace : Measurable (fun x => ((hessianMatrix u x)⁻¹ * hessianMatrix f x).trace) := by
    simpa only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply] using hsum
  have hdrift : Continuous (fun x => fderiv ℝ V (gradient u x) (gradient f x)) :=
    ((hV.continuous_fderiv one_ne_zero).comp hG.continuous).clm_apply
      (BakryEmery.continuous_gradient hf)
  exact htrace.fun_sub hdrift.measurable
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
 theorem solution {n : ℕ}
    {u V : EuclideanSpace ℝ (Fin n) → ℝ} {G LF : NNReal}
    (hu : ContDiff ℝ 1 u) (hG : LipschitzWith G (gradient u))
    (hV : ContDiff ℝ 1 V)
    (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
    (hPD : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (FunctionalInequalities.Probability.Stein.hessianMatrix u x).PosDef)
    (hnorm : ∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 1)
    (hsub : ∀ t : ℝ, IsCompact {x | u x ≤ t})
    {D : ℝ} (hD : 0 ≤ D)
    (hdrift : ∀ x, |(n : ℝ) - fderiv ℝ V (gradient u x) (gradient u x)| ≤ D)
    (c : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R →
      let χ := fun x => Real.smoothTransition (2 - (u x - c) / R)
      let Lχ := fun x => ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * FunctionalInequalities.Probability.Stein.hessianMatrix χ x).trace -
        fderiv ℝ V (gradient u x) (gradient χ x)
      Integrable (fun x => Lχ x * Real.exp (-u x))
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      (∫ x, |Lχ x| * Real.exp (-u x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤ C / R := by
  classical
  let η : ℝ → ℝ := fun t => Real.smoothTransition (2 - t)
  obtain ⟨hη, _, _, _, _, _, _, _, B, hB, hBbound⟩ :=
    FunctionalInequalities.Analysis.smoothTransition_two_sub_cutoff_408915f
  obtain ⟨w, hw, _, hw0, hws, hwbound⟩ :=
    FunctionalInequalities.Analysis.exists_majorant_abs_deriv_deriv_smoothTransition_two_sub_408915f
  have hIw : 0 ≤ ∫ t in (0 : ℝ)..3, w t :=
    intervalIntegral.integral_nonneg_of_forall (by norm_num) hw0
  refine ⟨D * (B + ∫ t in (0 : ℝ)..3, w t),
    mul_nonneg hD (add_nonneg hB hIw), ?_⟩
  intro R hR
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hRi : 0 ≤ R⁻¹ := inv_nonneg.mpr hRpos.le
  let ζ : ℝ → ℝ := fun s => η ((s - c) / R)
  let χ : EuclideanSpace ℝ (Fin n) → ℝ := fun x => ζ (u x)
  let L : EuclideanSpace ℝ (Fin n) → ℝ := fun x =>
    ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * FunctionalInequalities.Probability.Stein.hessianMatrix χ x).trace -
      fderiv ℝ V (gradient u x) (gradient χ x)
  let Γ : EuclideanSpace ℝ (Fin n) → ℝ := fun x =>
    ∑ i : Fin n, ∑ j : Fin n, (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j *
      fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) *
      fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j)
  let q : EuclideanSpace ℝ (Fin n) → ℝ := fun x =>
    (R ^ 2)⁻¹ * w ((u x - c) / R) * Γ x * Real.exp (-u x)
  change Integrable (fun x => L x * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    (∫ x, |L x| * Real.exp (-u x)
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
        D * (B + ∫ t in (0 : ℝ)..3, w t) / R
  have hζ : ContDiff ℝ ∞ ζ :=
    hη.comp ((contDiff_id.sub contDiff_const).div_const R)
  have hζ1 : ContDiff ℝ 1 ζ :=
    hζ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hζ2 : ContDiff ℝ 2 ζ :=
    hζ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hL : Measurable L :=
    measurable_inverse_hessian_generator_of_contDiff_one hG hV (hζ1.comp hu)
  have hexpm : Measurable (fun x => Real.exp (-u x)) :=
    (Real.continuous_exp.comp hu.continuous.neg).measurable
  have hexp := FunctionalInequalities.Analysis.BakryEmery.integrable_exp_neg_of_integral_eq_one
    (volume : Measure (EuclideanSpace ℝ (Fin n))) u hnorm
  have hp := integrable_majorant_inverse_energy_and_integral_le
    hu hG hV hF hdet hnorm hsub hD hdrift hw hw0 hws hRpos c
  have hq : Integrable q (volume : Measure (EuclideanSpace ℝ (Fin n))) := hp.1
  have hqbound :
      (∫ x, q x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
        D * (R⁻¹ * ∫ t in (0 : ℝ)..3, w t) := hp.2
  have hfirst := hexp.const_mul (B * D / R)
  have hmajor : Integrable
      (fun x => (B * D / R) * Real.exp (-u x) + q x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := hfirst.add hq
  have hdet0 : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det ≠ 0 :=
    hdet.mono fun x hx => hx.trans_ne (Real.exp_ne_zero _)
  have hgen := ae_inverse_hessian_generator_comp_profile hu hG hζ2 hdet0 V
  have hpoint : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      |L x| * Real.exp (-u x) ≤
        (B * D / R) * Real.exp (-u x) + q x := by
    filter_upwards [hgen, hPD] with x hx hPx
    change L x =
      deriv ζ (u x) * ((n : ℝ) - fderiv ℝ V (gradient u x) (gradient u x)) +
        deriv (deriv ζ) (u x) * Γ x at hx
    have hΓ : 0 ≤ Γ x :=
      sum_inverse_quadratic_nonneg_of_posDef (FunctionalInequalities.Probability.Stein.hessianMatrix u x) hPx
        (fun i => fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i))
    have hd :
        deriv ζ (u x) = R⁻¹ * deriv η ((u x - c) / R) ∧
        deriv (deriv ζ) (u x) =
          (R⁻¹) ^ 2 * deriv (deriv η) ((u x - c) / R) :=
      FunctionalInequalities.Analysis.deriv_comp_sub_div_and_deriv_deriv_408915f η c R (u x)
    have habs1 :
        |R⁻¹ * deriv η ((u x - c) / R) *
          ((n : ℝ) - fderiv ℝ V (gradient u x) (gradient u x))| ≤ B * D / R := by
      calc
        _ = R⁻¹ * (|deriv η ((u x - c) / R)| *
            |(n : ℝ) - fderiv ℝ V (gradient u x) (gradient u x)|) := by
          rw [abs_mul, abs_mul, abs_of_nonneg hRi]
          ring
        _ ≤ R⁻¹ * (B * D) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul (hBbound ((u x - c) / R)).1 (hdrift x)
              (abs_nonneg _) hB) hRi
        _ = B * D / R := by
          rw [div_eq_mul_inv]
          ring
    have habs2 :
        |(R⁻¹) ^ 2 * deriv (deriv η) ((u x - c) / R) * Γ x| ≤
          (R ^ 2)⁻¹ * w ((u x - c) / R) * Γ x := by
      rw [abs_mul, abs_mul, abs_of_nonneg hΓ,
        abs_of_nonneg (sq_nonneg R⁻¹), inv_pow]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hwbound ((u x - c) / R))
          (inv_nonneg.mpr (sq_nonneg R))) hΓ
    calc
      |L x| * Real.exp (-u x) =
          |R⁻¹ * deriv η ((u x - c) / R) *
              ((n : ℝ) - fderiv ℝ V (gradient u x) (gradient u x)) +
            (R⁻¹) ^ 2 * deriv (deriv η) ((u x - c) / R) * Γ x| *
              Real.exp (-u x) := by rw [hx, hd.1, hd.2]
      _ ≤ (|R⁻¹ * deriv η ((u x - c) / R) *
              ((n : ℝ) - fderiv ℝ V (gradient u x) (gradient u x))| +
            |(R⁻¹) ^ 2 * deriv (deriv η) ((u x - c) / R) * Γ x|) *
              Real.exp (-u x) :=
        mul_le_mul_of_nonneg_right (abs_add_le _ _) (Real.exp_pos _).le
      _ ≤ (B * D / R + (R ^ 2)⁻¹ * w ((u x - c) / R) * Γ x) *
              Real.exp (-u x) :=
        mul_le_mul_of_nonneg_right (add_le_add habs1 habs2) (Real.exp_pos _).le
      _ = (B * D / R) * Real.exp (-u x) + q x := by
        dsimp only [q]
        ring
  have hweighted : Integrable (fun x => L x * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hmajor.mono' (hL.fun_mul hexpm).aestronglyMeasurable
      (hpoint.mono fun x hx => by
        simpa only [Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (Real.exp_pos (-u x)).le] using hx)
  have habsweighted : Integrable (fun x => |L x| * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hweighted.abs.congr (Filter.Eventually.of_forall fun x => by
      change |L x * Real.exp (-u x)| = |L x| * Real.exp (-u x)
      rw [abs_mul, abs_of_nonneg (Real.exp_pos (-u x)).le])
  refine ⟨hweighted, ?_⟩
  calc
    _ ≤ ∫ x, (B * D / R) * Real.exp (-u x) + q x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) :=
      integral_mono_ae habsweighted hmajor hpoint
    _ = B * D / R + ∫ x, q x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      rw [integral_add hfirst hq, integral_const_mul, hnorm, mul_one]
    _ ≤ B * D / R + D * (R⁻¹ * ∫ t in (0 : ℝ)..3, w t) :=
      add_le_add le_rfl hqbound
    _ = D * (B + ∫ t in (0 : ℝ)..3, w t) / R := by
      simp only [div_eq_mul_inv]
      ring
