-- Prove2me | solution 1 for FunctionalInequalities.Analysis.ae_hessian_increment_le_generator_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:04:16.311978+00:00
-- url     : https://prove2.me/submissions/c2a140c9-cc30-4d11-99e4-a5651a3668a3

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Alexandrov
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Proximal
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Subgradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Viscosity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_Coordinates
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Line_BrunnMinkowski
import Mathlib
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.EReal.Operations
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic
import Theorems.Thm_FunctionalInequalities_Analysis_log_det_add_frobenius_sq_le_408915f

noncomputable section
open Set Metric Filter
open scoped RealInnerProductSpace Topology
open FunctionalInequalities.Probability.Stein
section LN11AHessianIncrementCoercivity
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace
open FunctionalInequalities.Probability.Stein
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
private lemma FunctionalInequalities.Analysis.increment_fderiv {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : Differentiable ℝ u)
    (h : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun y => u (y + h) + u (y - h) - 2 * u y) =
      fun y => fderiv ℝ u (y + h) + fderiv ℝ u (y - h) -
        (fderiv ℝ u y + fderiv ℝ u y) := by
  funext y
  have hp : DifferentiableAt ℝ (fun z => u (z + h)) y :=
    (hu (y + h)).comp y (differentiableAt_id.add_const h)
  have hm : DifferentiableAt ℝ (fun z => u (z - h)) y :=
    (hu (y - h)).comp y (differentiableAt_id.sub_const h)
  simp only [two_mul]
  rw [fderiv_fun_sub (hp.fun_add hm) ((hu y).fun_add (hu y)),
    fderiv_fun_add hp hm, fderiv_fun_add (hu y) (hu y),
    fderiv_comp_add_right]
  simpa only [sub_eq_add_neg] using
    congrArg
      (fun q => fderiv ℝ u (y + h) + q - (fderiv ℝ u y + fderiv ℝ u y))
      (fderiv_comp_add_right (𝕜 := ℝ) (f := u) (x := y) (-h))
private lemma FunctionalInequalities.Analysis.increment_gradient {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : Differentiable ℝ u)
    (h x : EuclideanSpace ℝ (Fin n)) :
    gradient (fun y => u (y + h) + u (y - h) - 2 * u y) x =
      gradient u (x + h) + gradient u (x - h) - 2 • gradient u x := by
  change (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
    (fderiv ℝ (fun y => u (y + h) + u (y - h) - 2 * u y) x) = _
  rw [increment_fderiv hu h]
  simp only [map_sub, map_add, gradient, two_smul]
private lemma FunctionalInequalities.Analysis.increment_hessian {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : Differentiable ℝ u)
    (h x : EuclideanSpace ℝ (Fin n))
    (hx : DifferentiableAt ℝ (fderiv ℝ u) x)
    (hp : DifferentiableAt ℝ (fderiv ℝ u) (x + h))
    (hm : DifferentiableAt ℝ (fderiv ℝ u) (x - h)) :
    hessianMatrix (fun y => u (y + h) + u (y - h) - 2 * u y) x =
      hessianMatrix u (x + h) + hessianMatrix u (x - h) -
        2 • hessianMatrix u x := by
  have dp : DifferentiableAt ℝ (fun y => fderiv ℝ u (y + h)) x :=
    hp.comp x (differentiableAt_id.add_const h)
  have dm : DifferentiableAt ℝ (fun y => fderiv ℝ u (y - h)) x :=
    hm.comp x (differentiableAt_id.sub_const h)
  ext i j
  change
    fderiv ℝ (fderiv ℝ (fun y => u (y + h) + u (y - h) - 2 * u y)) x _ _ = _
  rw [increment_fderiv hu h,
    fderiv_fun_sub (dp.fun_add dm) (hx.fun_add hx),
    fderiv_fun_add dp dm, fderiv_fun_add hx hx, fderiv_comp_add_right]
  have ht :
      fderiv ℝ (fun y => fderiv ℝ u (y - h)) x =
        fderiv ℝ (fderiv ℝ u) (x - h) := by
    simpa only [sub_eq_add_neg] using
      (fderiv_comp_add_right (𝕜 := ℝ) (f := fderiv ℝ u) (x := x) (-h))
  rw [ht]
  simp [hessianMatrix, bilinearIteratedFDerivTwo, two_smul]
private lemma FunctionalInequalities.Analysis.convex_fderiv_le_sub {n : ℕ}
    {V : EuclideanSpace ℝ (Fin n) → ℝ}
    (hV : Differentiable ℝ V) (hc : ConvexOn ℝ univ V)
    (c a : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ V c (a - c) ≤ V a - V c := by
  let q : ℝ → ℝ := fun t => V (c + t • (a - c))
  have hq : ConvexOn ℝ univ q := by
    refine ⟨convex_univ, ?_⟩
    intro s _ t _ α β hα hβ hab
    have he₀ :
        (α + β) • c + (α * s + β * t) • (a - c) =
          α • (c + s • (a - c)) + β • (c + t • (a - c)) := by
      module
    have he :
        c + (α * s + β * t) • (a - c) =
          α • (c + s • (a - c)) + β • (c + t • (a - c)) := by
      simpa only [hab, one_smul] using he₀
    simpa only [q, smul_eq_mul, he] using
      hc.2 (mem_univ (c + s • (a - c))) (mem_univ (c + t • (a - c)))
        hα hβ hab
  have hd : HasDerivAt q (fderiv ℝ V c (a - c)) 0 := by
    have hl :=
      ((hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).smul_const (a - c)).const_add c
    have hv :
        HasFDerivAt V (fderiv ℝ V c) (c + (0 : ℝ) • (a - c)) := by
      simpa using (hV c).hasFDerivAt
    simpa [q, Function.comp_def] using hv.comp_hasDerivAt 0 hl
  have hs :=
    hq.le_slope_of_hasDerivAt (mem_univ 0) (mem_univ 1) (by norm_num) hd
  simpa [q, slope] using hs
/-- **Three-point log-det concavity** (weak Letwin route): for positive definite `A, B₊, B₋ ≤ K·Id`,
`(‖B₊ − A‖²_F + ‖B₋ − A‖²_F)/(2K²) ≤ tr(A⁻¹(B₊ + B₋ − 2A)) − log det B₊ − log det B₋ + 2 log det A`. -/
theorem FunctionalInequalities.Analysis.frobenius_add_frobenius_le_trace_sub_log_det {n : ℕ}
    {A Bp Bm : Matrix (Fin n) (Fin n) ℝ} {K : ℝ} (hA : A.PosDef) (hBp : Bp.PosDef) (hBm : Bm.PosDef)
    (hAK : (K • (1 : Matrix (Fin n) (Fin n) ℝ) - A).PosSemidef)
    (hBpK : (K • (1 : Matrix (Fin n) (Fin n) ℝ) - Bp).PosSemidef)
    (hBmK : (K • (1 : Matrix (Fin n) (Fin n) ℝ) - Bm).PosSemidef) :
    ((∑ i, ∑ j, (Bp - A) i j ^ 2) + ∑ i, ∑ j, (Bm - A) i j ^ 2) / (2 * K ^ 2) ≤
      (A⁻¹ * (Bp + Bm - 2 • A)).trace - Real.log Bp.det - Real.log Bm.det + 2 * Real.log A.det := by
  have hp := log_det_add_frobenius_sq_le_408915f hA hBp hAK hBpK
  have hm := log_det_add_frobenius_sq_le_408915f hA hBm hAK hBmK
  have he : Bp + Bm - 2 • A = (Bp - A) + (Bm - A) := by
    rw [two_smul]
    abel
  rw [he, Matrix.mul_add, Matrix.trace_add, add_div]
  linarith
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- **Pointwise coercivity of Hessian increments for a `C^{1,1}` Monge–Ampère solution** (weak Letwin route; KLS500 `weak_moment_centered_difference_coercivity_ae`): if a.e. `∇²u` is positive definite, `≤ K·Id`, and
`log det ∇²u = −u + V(∇u)` with `V` convex and differentiable, then for every `h`, at a.e. `x`, with
`w := u(· + h) + u(· − h) − 2u` and `H := ∇²u`,
`(‖H(x+h) − H(x)‖²_F + ‖H(x−h) − H(x)‖²_F)/(2K²) ≤ tr(H(x)⁻¹ ∇²w(x)) − DV(∇u(x))(∇w(x)) + w(x)`. -/
theorem solution {n : ℕ} {u V : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) {G : NNReal} (hG : LipschitzWith G (gradient u))
    (hV : Differentiable ℝ V) (hVc : ConvexOn ℝ univ V) {K : ℝ}
    (hdata : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (FunctionalInequalities.Probability.Stein.hessianMatrix u x).PosDef ∧
      Real.log (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det = -u x + V (gradient u x) ∧
      (K • (1 : Matrix (Fin n) (Fin n) ℝ) - FunctionalInequalities.Probability.Stein.hessianMatrix u x).PosSemidef)
    (h : EuclideanSpace ℝ (Fin n)) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ((∑ i, ∑ j, (FunctionalInequalities.Probability.Stein.hessianMatrix u (x + h) - FunctionalInequalities.Probability.Stein.hessianMatrix u x) i j ^ 2) +
          ∑ i, ∑ j, (FunctionalInequalities.Probability.Stein.hessianMatrix u (x - h) - FunctionalInequalities.Probability.Stein.hessianMatrix u x) i j ^ 2) / (2 * K ^ 2) ≤
        ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ *
            FunctionalInequalities.Probability.Stein.hessianMatrix (fun y => u (y + h) + u (y - h) - 2 * u y) x).trace -
          fderiv ℝ V (gradient u x) (gradient (fun y => u (y + h) + u (y - h) - 2 * u y) x) +
          (u (x + h) + u (x - h) - 2 * u x) := by
  have hud : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hd :
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        DifferentiableAt ℝ (fderiv ℝ u) x := by
    filter_upwards [hG.ae_differentiableAt
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))] with x hx
    rw [← toDual_comp_gradient]
    exact
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).differentiable.differentiableAt.comp
        x hx
  have hgood := hdata.and hd
  have hplus :=
    (measurePreserving_add_right
      (volume : Measure (EuclideanSpace ℝ (Fin n))) h).quasiMeasurePreserving.ae hgood
  have hminus :=
    (measurePreserving_add_right
      (volume : Measure (EuclideanSpace ℝ (Fin n))) (-h)).quasiMeasurePreserving.ae hgood
  filter_upwards [hgood, hplus, hminus] with x hx hp hm
  simp only [← sub_eq_add_neg] at hm
  have hH := increment_hessian hud h x hx.2 hp.2 hm.2
  have hg := increment_gradient hud h x
  have hlog :=
    FunctionalInequalities.Analysis.frobenius_add_frobenius_le_trace_sub_log_det
      hx.1.1 hp.1.1 hm.1.1 hx.1.2.2 hp.1.2.2 hm.1.2.2
  rw [hp.1.2.1, hm.1.2.1, hx.1.2.1] at hlog
  have hVp := convex_fderiv_le_sub hV hVc (gradient u x) (gradient u (x + h))
  have hVm := convex_fderiv_le_sub hV hVc (gradient u x) (gradient u (x - h))
  have hconv :
      fderiv ℝ V (gradient u x)
          (gradient u (x + h) + gradient u (x - h) - 2 • gradient u x) ≤
        V (gradient u (x + h)) + V (gradient u (x - h)) -
          2 * V (gradient u x) := by
    simp only [two_smul, map_sub, map_add] at hVp hVm ⊢
    linarith
  rw [hH, hg]
  linarith only [hlog, hconv]
