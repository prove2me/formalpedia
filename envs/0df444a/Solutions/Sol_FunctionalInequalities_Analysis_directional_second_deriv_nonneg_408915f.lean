-- Prove2me | solution 1 for FunctionalInequalities.Analysis.directional_second_deriv_nonneg_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:22:32.451985+00:00
-- url     : https://prove2.me/submissions/faf3c478-0db3-4223-90b9-7708eddbbcd9

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

noncomputable section
open Set Metric Filter
open scoped RealInnerProductSpace Topology
open FunctionalInequalities.Probability.Stein
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
 lemma solution
    {n : ℕ} {u ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hconv : ConvexOn ℝ univ u) {x₀ : EuclideanSpace ℝ (Fin n)}
    (hψ : ContDiffAt ℝ 2 ψ x₀) (hcontact : u x₀ = ψ x₀)
    (htouch : ∀ᶠ x in 𝓝 x₀, u x ≤ ψ x)
    (v : EuclideanSpace ℝ (Fin n)) :
    0 ≤ bilinearIteratedFDerivTwo ℝ ψ x₀ v v := by
  let L : ℝ → EuclideanSpace ℝ (Fin n) := fun t => x₀ + t • v
  let q : ℝ → ℝ := fun t => ψ (L t)
  let p : ℝ → ℝ := fun t => (fderiv ℝ ψ (L t)) v
  let r : ℝ → ℝ := fun t => q t + q (-t)
  have hL (t : ℝ) : HasDerivAt L v t := by
    simpa [L] using
      ((hasDerivAt_id (𝕜 := ℝ) t).smul_const v).const_add x₀
  have hLcont : Tendsto L (𝓝 0) (𝓝 x₀) := by
    simpa [L] using (hL 0).continuousAt.tendsto
  have hneg : Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by
    simpa using
      (continuousAt_neg : ContinuousAt (fun t : ℝ => -t) (0 : ℝ)).tendsto
  have hψevent :
      ∀ᶠ t : ℝ in 𝓝 0, ContDiffAt ℝ 2 ψ (L t) :=
    hLcont.eventually (hψ.eventually (by norm_num))
  have hqevent : ∀ᶠ t : ℝ in 𝓝 0, HasDerivAt q (p t) t := by
    filter_upwards [hψevent] with t ht
    have h :=
      (ht.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hL t)
    simpa only [q, p, Function.comp_def] using h
  have hrderiv : deriv r =ᶠ[𝓝 0] (fun t => p t - p (-t)) := by
    filter_upwards [hqevent, hneg.eventually hqevent] with t ht htneg
    have hn : HasDerivAt (fun s : ℝ => q (-s)) (-p (-t)) t := by
      simpa [Function.comp_def] using
        htneg.comp t (hasDerivAt_id (𝕜 := ℝ) t).neg
    simpa only [r, sub_eq_add_neg] using (ht.fun_add hn).deriv
  have hfd : ContDiffAt ℝ 1 (fderiv ℝ ψ) x₀ :=
    hψ.fderiv_right (m := 1) (n := 2) (by norm_num)
  have hpf : HasFDerivAt (fderiv ℝ ψ)
      (fderiv ℝ (fderiv ℝ ψ) x₀) x₀ :=
    (hfd.differentiableAt (by norm_num)).hasFDerivAt
  have hp0 :
      HasDerivAt p (bilinearIteratedFDerivTwo ℝ ψ x₀ v v) 0 := by
    have hpf' : HasFDerivAt (fderiv ℝ ψ)
        (fderiv ℝ (fderiv ℝ ψ) x₀) (L 0) := by
      simpa [L] using hpf
    have hcomp := hpf'.comp_hasDerivAt 0 (hL 0)
    have happ := hcomp.clm_apply (hasDerivAt_const (x := (0 : ℝ)) v)
    simpa [p, L, bilinearIteratedFDerivTwo, Function.comp_def] using happ
  have hpneg :
      HasDerivAt (fun t => p (-t))
        (-(bilinearIteratedFDerivTwo ℝ ψ x₀ v v)) 0 := by
    have hp0' : HasDerivAt p
        (bilinearIteratedFDerivTwo ℝ ψ x₀ v v) (-(0 : ℝ)) := by
      simpa only [neg_zero] using hp0
    simpa [Function.comp_def] using
      hp0'.comp 0 (hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).neg
  have hpdiff :
      HasDerivAt (fun t => p t - p (-t))
        (2 * bilinearIteratedFDerivTwo ℝ ψ x₀ v v) 0 := by
    simpa [two_mul] using hp0.fun_sub hpneg
  have hsecond :
      deriv (deriv r) 0 =
        2 * bilinearIteratedFDerivTwo ℝ ψ x₀ v v := by
    calc
      deriv (deriv r) 0 =
          deriv (fun t => p t - p (-t)) 0 := hrderiv.deriv_eq
      _ = 2 * bilinearIteratedFDerivTwo ℝ ψ x₀ v v := hpdiff.deriv
  have hq0 : HasDerivAt q ((fderiv ℝ ψ x₀) v) 0 := by
    have hψ' : HasFDerivAt ψ (fderiv ℝ ψ x₀) (L 0) := by
      simpa [L] using (hψ.differentiableAt (by norm_num)).hasFDerivAt
    simpa only [q, Function.comp_def] using hψ'.comp_hasDerivAt 0 (hL 0)
  have hqneg0 :
      HasDerivAt (fun t => q (-t)) (-((fderiv ℝ ψ x₀) v)) 0 := by
    have hq0' : HasDerivAt q ((fderiv ℝ ψ x₀) v) (-(0 : ℝ)) := by
      simpa only [neg_zero] using hq0
    simpa [Function.comp_def] using
      hq0'.comp 0 (hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).neg
  have hr0 : deriv r 0 = 0 := by
    simpa [r] using (hq0.fun_add hqneg0).deriv
  have hrcont : ContinuousAt r 0 :=
    (hq0.fun_add hqneg0).continuousAt
  have hmin : IsLocalMin r 0 := by
    change ∀ᶠ t : ℝ in 𝓝 0, r 0 ≤ r t
    have hLt : ∀ᶠ t : ℝ in 𝓝 0, u (L t) ≤ ψ (L t) :=
      hLcont.eventually htouch
    filter_upwards [hLt, hneg.eventually hLt] with t ht htneg
    have hc := hconv.2 (mem_univ (L t)) (mem_univ (L (-t)))
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    have hmid :
        (1 / 2 : ℝ) • L t + (1 / 2 : ℝ) • L (-t) = x₀ := by
      dsimp [L]
      module
    rw [hmid] at hc
    change u x₀ ≤ (1 / 2 : ℝ) * u (L t) + (1 / 2 : ℝ) * u (L (-t)) at hc
    rw [hcontact] at hc
    have hrzero : r 0 = 2 * ψ x₀ := by
      simp [r, q, L, two_mul]
    rw [hrzero]
    change 2 * ψ x₀ ≤ ψ (L t) + ψ (L (-t))
    linarith
  by_contra hA
  have hA' : bilinearIteratedFDerivTwo ℝ ψ x₀ v v < 0 :=
    lt_of_not_ge hA
  have hmax : IsLocalMax r 0 :=
    isLocalMax_of_deriv_deriv_neg (by linarith [hsecond]) hr0 hrcont
  change ∀ᶠ t : ℝ in 𝓝 0, r t ≤ r 0 at hmax
  change ∀ᶠ t : ℝ in 𝓝 0, r 0 ≤ r t at hmin
  have heq : r =ᶠ[𝓝 0] (fun _ : ℝ => r 0) := by
    filter_upwards [hmin, hmax] with t htmin htmax
    exact le_antisymm htmax htmin
  rcases _root_.mem_nhds_iff.mp heq with ⟨s, hs, hso, h0s⟩
  have hderiv : deriv r =ᶠ[𝓝 0] (fun _ : ℝ => 0) := by
    filter_upwards [hso.mem_nhds h0s] with t ht
    have hloc : r =ᶠ[𝓝 t] (fun _ : ℝ => r 0) := by
      filter_upwards [hso.mem_nhds ht] with y hy
      exact hs hy
    simpa using hloc.deriv_eq
  have hz : deriv (deriv r) 0 = 0 := by
    simpa using hderiv.deriv_eq
  linarith
