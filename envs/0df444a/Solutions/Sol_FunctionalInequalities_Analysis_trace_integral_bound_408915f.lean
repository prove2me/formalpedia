-- Prove2me | solution 1 for FunctionalInequalities.Analysis.trace_integral_bound_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:24:41.33683+00:00
-- url     : https://prove2.me/submissions/7be1a159-c478-4433-b15d-9cd9f53a96fd

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
import Theorems.Thm_FunctionalInequalities_Analysis_expansion_secondDifference_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_forall_posDef_add_log_det_le_trace_iff_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_integral_mul_le_integral_mul_sum_iteratedFDeriv_408915f

noncomputable section
open Set Metric Filter
open scoped RealInnerProductSpace Topology
open FunctionalInequalities.Probability.Stein
section LT12D8MollifiedLogdetBound
open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal Topology
open FunctionalInequalities.Probability.Stein
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
private lemma FunctionalInequalities.Analysis.matrix_quadratic_sum {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    ⟪v, Matrix.toEuclideanLin A v⟫ =
      ∑ i, ∑ j, v.ofLp i * (A i j * v.ofLp j) := by
  rw [Matrix.toLpLin_apply 2 2, PiLp.inner_apply]
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial,
    Matrix.mulVec, dotProduct, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring
private lemma FunctionalInequalities.Analysis.trace_spectral_quadratic {n : ℕ}
    {J : Matrix (Fin n) (Fin n) ℝ} (hJ : J.IsHermitian)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (J * A).trace =
      ∑ i, hJ.eigenvalues i *
        ⟪hJ.eigenvectorBasis i, Matrix.toEuclideanLin A (hJ.eigenvectorBasis i)⟫ := by
  classical
  let U : Matrix (Fin n) (Fin n) ℝ := hJ.eigenvectorUnitary
  let D := Matrix.diagonal hJ.eigenvalues
  have hs : J = U * D * star U := by
    simpa only [Unitary.conjStarAlgAut_apply, Function.comp_def,
      RCLike.ofReal_real_eq_id, id_eq] using hJ.spectral_theorem
  have he (i : Fin n) :
      (star U * A * U) i i =
        ⟪hJ.eigenvectorBasis i, Matrix.toEuclideanLin A (hJ.eigenvectorBasis i)⟫ := by
    rw [matrix_quadratic_sum]
    simp only [Matrix.mul_apply, Matrix.star_apply, star_trivial, Finset.sum_mul,
      U, Matrix.IsHermitian.eigenvectorUnitary_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  calc
    (J * A).trace = (U * D * star U * A).trace := by rw [hs]
    _ = (D * (star U * A) * U).trace := by
      rw [Matrix.mul_assoc U D (star U), Matrix.mul_assoc U (D * star U) A,
        Matrix.trace_mul_comm U ((D * star U) * A), Matrix.mul_assoc D (star U) A]
    _ = (D * (star U * A * U)).trace := by rw [Matrix.mul_assoc]
    _ = _ := by
      simp only [D, Matrix.trace, Matrix.diag, Matrix.diagonal_mul, he]
set_option maxHeartbeats 800000 in
private lemma FunctionalInequalities.Analysis.second_weight_integrable {n : ℕ}
    {u χ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : Continuous u) (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ)
    (v : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun y => u y * iteratedFDeriv ℝ 2 χ y (fun _ => v)) volume := by
  let L := ContinuousMultilinearMap.apply ℝ
    (fun _ : Fin 2 => EuclideanSpace ℝ (Fin n)) ℝ (fun _ => v)
  have hc : Continuous (fun y => iteratedFDeriv ℝ 2 χ y (fun _ => v)) := by
    change Continuous (L ∘ iteratedFDeriv ℝ 2 χ)
    exact L.continuous.comp (ContDiff.continuous_iteratedFDeriv (by norm_num) hχ)
  have hs : HasCompactSupport (fun y => iteratedFDeriv ℝ 2 χ y (fun _ => v)) := by
    change HasCompactSupport (L ∘ iteratedFDeriv ℝ 2 χ)
    exact (hχc.iteratedFDeriv 2).comp_left (g := L) (map_zero L)
  exact (hu.mul hc).integrable_of_hasCompactSupport hs.mul_left
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
set_option maxHeartbeats 800000 in
 lemma solution {n : ℕ}
    {u F χ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hconv : ConvexOn ℝ univ u) (hF : Continuous F)
    (hae : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ∃ B : Matrix (Fin n) (Fin n) ℝ, B.IsHermitian ∧ B.PosDef ∧
        F y ≤ Real.log B.det ∧ ∃ g : EuclideanSpace ℝ (Fin n),
          ∀ ε > 0, ∀ᶠ z in 𝓝 y,
            |u z - FunctionalInequalities.Analysis.quadraticAt B y g (u y) z| ≤ ε * ‖z - y‖ ^ 2)
    (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ) (hχ0 : ∀ y, 0 ≤ χ y)
    (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : ∀ v : EuclideanSpace ℝ (Fin n),
      ⟪v, Matrix.toEuclideanLin H v⟫ =
        ∫ y, u y * iteratedFDeriv ℝ 2 χ y (fun _ => v))
    (J : Matrix (Fin n) (Fin n) ℝ) (hJ : J.PosDef) :
    (∫ y, (F y + Real.log J.det + n) * χ y) ≤ (J * H).trace := by
  classical
  let v := hJ.isHermitian.eigenvectorBasis
  let c := hJ.isHermitian.eigenvalues
  have hc (i : Fin n) : 0 ≤ c i := (hJ.eigenvalues_pos i).le
  have hg : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ∀ ε > 0, ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ →
        (F y + Real.log J.det + n) - ε ≤
          ∑ i, c i * ((u (y + t • v i) + u (y - t • v i) - 2 * u y) / t ^ 2) := by
    filter_upwards [hae] with y hy
    obtain ⟨B, _, hB, hFB, g, hexp⟩ := hy
    have hlim :
        Tendsto (fun t : ℝ => ∑ i, c i *
          ((u (y + t • v i) + u (y - t • v i) - 2 * u y) / t ^ 2))
          (𝓝[>] 0) (𝓝 ((J * B).trace)) := by
      rw [trace_spectral_quadratic hJ.isHermitian B]
      exact tendsto_finsetSum _ fun i _ =>
        (FunctionalInequalities.Analysis.expansion_secondDifference_408915f hexp (v i)).const_mul (c i)
    have htr : F y + Real.log J.det + n ≤ (J * B).trace :=
      ((FunctionalInequalities.Analysis.forall_posDef_add_log_det_le_trace_iff_408915f hB.posSemidef (F y)).mpr
        ⟨hB, (Real.le_log_iff_exp_le hB.det_pos).mp hFB⟩) J hJ
    intro ε hε
    have hev := hlim.eventually_const_lt (show
      F y + Real.log J.det + n - ε < (J * B).trace by linarith)
    obtain ⟨δ, hδ, hd⟩ := Metric.mem_nhdsWithin_iff.mp hev
    refine ⟨δ, hδ, fun t ht htd => (hd ⟨?_, ht⟩).le⟩
    simpa only [mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht] using htd
  have hi := FunctionalInequalities.Analysis.integral_mul_le_integral_mul_sum_iteratedFDeriv_408915f hconv
    (fun i : Fin n => v i) hc hχ hχc hχ0
    ((hF.add continuous_const).add continuous_const).aestronglyMeasurable hg
  have hu : Continuous u := continuousOn_univ.mp (hconv.continuousOn isOpen_univ)
  have hdi (i : Fin n) := second_weight_integrable hu hχ hχc (v i)
  have he :
      (∫ y, u y * ∑ i, c i * iteratedFDeriv ℝ 2 χ y (fun _ => v i)) =
        (J * H).trace := by
    calc
      _ = ∫ y, ∑ i, c i * (u y * iteratedFDeriv ℝ 2 χ y (fun _ => v i)) := by
        apply integral_congr_ae
        filter_upwards [] with y
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = ∑ i, c i * ∫ y, u y * iteratedFDeriv ℝ 2 χ y (fun _ => v i) := by
        rw [integral_finsetSum _ (fun i _ => (hdi i).const_mul (c i))]
        simp only [integral_const_mul]
      _ = _ := by
        rw [trace_spectral_quadratic hJ.isHermitian H]
        apply Finset.sum_congr rfl
        intro i _
        rw [hH]
  exact he ▸ hi
