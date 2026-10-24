-- Prove2me | solution 1 for FunctionalInequalities.Analysis.exists_hessian_cutoff_sq_difference_bound_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:25:08.623704+00:00
-- url     : https://prove2.me/submissions/eb4464ba-c941-4049-bca3-f6279493a646

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_Weak
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_WeakHessian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Alexandrov
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Proximal
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Subgradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Viscosity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_LipschitzBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_DeterminantDerivative
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Piola
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_Coordinates
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_WeakDerivative_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Line_BrunnMinkowski
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
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
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
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Semicontinuity.Basic
import Theorems.Thm_FunctionalInequalities_Analysis_exists_smooth_compact_translate_majorant_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_integrable_hessian_increment_energy_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_integral_mul_hessian_increment_le_408915f
import Theorems.Thm_FunctionalInequalities_Probability_Stein_memLp_cutoff_mul_hessianMatrix_entry_408915f
import Theorems.Thm_FunctionalInequalities_Probability_Stein_norm_hessianMatrix_entry_le_of_lipschitz_gradient_408915f

noncomputable section
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace
open FunctionalInequalities.Probability.Stein
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff RealInnerProductSpace
open FunctionalInequalities.Probability.Stein
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
private lemma FunctionalInequalities.Analysis.n11d3_entry_sq_le_total {n : ℕ}
    (P Q : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    P i j ^ 2 ≤
      (∑ k, ∑ l, P k l ^ 2) + ∑ k, ∑ l, Q k l ^ 2 := by
  classical
  have hj : P i j ^ 2 ≤ ∑ l, P i l ^ 2 :=
    Finset.single_le_sum (fun l _ => sq_nonneg (P i l)) (Finset.mem_univ j)
  have hi : (∑ l, P i l ^ 2) ≤ ∑ k, ∑ l, P k l ^ 2 :=
    Finset.single_le_sum
      (fun k _ => Finset.sum_nonneg (fun l _ => sq_nonneg (P k l)))
      (Finset.mem_univ i)
  exact (hj.trans hi).trans
    (le_add_of_nonneg_right
      (Finset.sum_nonneg
        (fun k _ => Finset.sum_nonneg (fun l _ => sq_nonneg (Q k l)))))
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
set_option maxHeartbeats 800000 in
/-- Produce the actual global L2 difference-quotient bound for a compact cutoff
times a Hessian entry from the original Monge-Ampere/increment hypotheses.
The bound is a conclusion, never a supplied regularity or energy premise. -/
theorem solution {n : ℕ}
    {u V χ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) (hconv : ConvexOn ℝ univ u) {G : NNReal}
    (hG : LipschitzWith G (gradient u)) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {LF : NNReal} (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
    {K : ℝ} (hK : 0 < K)
    (hdata : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (FunctionalInequalities.Probability.Stein.hessianMatrix u x).PosDef ∧
      Real.log (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det = -u x + V (gradient u x) ∧
      (K • (1 : Matrix (Fin n) (Fin n) ℝ) - FunctionalInequalities.Probability.Stein.hessianMatrix u x).PosSemidef)
    {D : ℝ} (hw : ∀ x h, u (x + h) + u (x - h) - 2 * u x ≤ D * ‖h‖ ^ 2)
    (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (i j : Fin n) (v : EuclideanSpace ℝ (Fin n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, t ≠ 0 → |t| ≤ 1 →
      (∫ x, (χ (x + t • v) * FunctionalInequalities.Probability.Stein.hessianMatrix u (x + t • v) i j -
        χ x * FunctionalInequalities.Probability.Stein.hessianMatrix u x i j) ^ 2) ≤ C * t ^ 2 := by
  classical
  obtain ⟨η, hη, hηc, hη0, hmajor⟩ :=
    FunctionalInequalities.Analysis.exists_smooth_compact_translate_majorant_408915f hu.continuous hχ.continuous hχc v
  have hη2 : ContDiff ℝ 2 η :=
    hη.of_le (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨L, hL⟩ :=
    ContDiff.lipschitzWith_of_hasCompactSupport hχc hχ one_ne_zero
  let H : EuclideanSpace ℝ (Fin n) → ℝ := fun x => FunctionalInequalities.Probability.Stein.hessianMatrix u x i j
  let q : EuclideanSpace ℝ (Fin n) → ℝ :=
    (tsupport η).indicator (fun _ => (1 : ℝ))
  have hqint : Integrable q (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (integrable_indicator_iff (isClosed_tsupport η).measurableSet).mpr
      (integrableOn_const hηc.isCompact.measure_lt_top.ne)
  have hq0 (x : EuclideanSpace ℝ (Fin n)) : 0 ≤ q x :=
    Set.indicator_nonneg (fun _ _ => zero_le_one) x
  let J : ℝ := ∫ x, q x
  have hJ : 0 ≤ J := integral_nonneg hq0
  let I : ℝ :=
    ∫ x, |η x + (((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * FunctionalInequalities.Probability.Stein.hessianMatrix η x).trace -
      fderiv ℝ V (gradient u x) (gradient η x))| * Real.exp (-u x)
  let A : ℝ := |2 * K ^ 2 * D * I| * ‖v‖ ^ 2
  let B : ℝ := ((G : ℝ) * (L : ℝ) * ‖v‖) ^ 2
  have hA : 0 ≤ A := mul_nonneg (abs_nonneg _) (sq_nonneg _)
  have hB : 0 ≤ B := sq_nonneg _
  let e : ℝ → EuclideanSpace ℝ (Fin n) → ℝ := fun t x =>
    η x *
      ((∑ k, ∑ l,
          (FunctionalInequalities.Probability.Stein.hessianMatrix u (x + t • v) - FunctionalInequalities.Probability.Stein.hessianMatrix u x) k l ^ 2) +
        ∑ k, ∑ l,
          (FunctionalInequalities.Probability.Stein.hessianMatrix u (x - t • v) - FunctionalInequalities.Probability.Stein.hessianMatrix u x) k l ^ 2) *
      Real.exp (-u x)
  have heint (t : ℝ) :
      Integrable (e t) (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    FunctionalInequalities.Analysis.integrable_hessian_increment_energy_408915f hu.continuous hG hη.continuous hηc (t • v)
  have hebound (t : ℝ) : (∫ x, e t x) ≤ A * t ^ 2 := by
    have hh :=
      FunctionalInequalities.Analysis.integral_mul_hessian_increment_le_408915f hu hconv hG hV hVc hF hK hdata
        hη2 hηc hη0 (t • v) (fun x => hw x (t • v))
    calc
      (∫ x, e t x) ≤ 2 * K ^ 2 * (D * ‖t • v‖ ^ 2) * I := hh
      _ = (2 * K ^ 2 * D * I) * ‖v‖ ^ 2 * t ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
        ring
      _ ≤ |2 * K ^ 2 * D * I| * ‖v‖ ^ 2 * t ^ 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _))
          (sq_nonneg _)
      _ = A * t ^ 2 := rfl
  have henvelope (t : ℝ) (ht : |t| ≤ 1) (x : EuclideanSpace ℝ (Fin n)) :
      χ (x + t • v) ^ 2 ≤ η x * Real.exp (-u x) := by
    calc
      χ (x + t • v) ^ 2 =
          (χ (x + t • v) ^ 2 * Real.exp (u x)) * Real.exp (-u x) := by
        rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
      _ ≤ η x * Real.exp (-u x) :=
        mul_le_mul_of_nonneg_right (hmajor t ht x) (Real.exp_pos _).le
  have hvanish (t : ℝ) (ht : |t| ≤ 1)
      (x : EuclideanSpace ℝ (Fin n)) (hx : x ∉ tsupport η) :
      χ (x + t • v) = 0 := by
    have hh := henvelope t ht x
    rw [image_eq_zero_of_notMem_tsupport hx, zero_mul] at hh
    exact sq_eq_zero_iff.mp (le_antisymm hh (sq_nonneg _))
  have hf : MemLp (fun x => χ x * H x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    FunctionalInequalities.Probability.Stein.memLp_cutoff_mul_hessianMatrix_entry_408915f hG i j hχ.continuous hχc
  refine ⟨2 * A + 2 * B * J, ?_, ?_⟩
  · positivity
  · intro t _ht0 ht
    have htranslated : MemLp (fun x => χ (x + t • v) * H (x + t • v)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
      hf.comp_measurePreserving (measurePreserving_add_right volume (t • v))
    have hdiff : MemLp
        (fun x => χ (x + t • v) * H (x + t • v) - χ x * H x) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
      htranslated.sub hf
    have hdiffint : Integrable
        (fun x => (χ (x + t • v) * H (x + t • v) - χ x * H x) ^ 2)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      simpa only [pow_two, Pi.mul_def] using hdiff.integrable_mul hdiff
    have hpoint (x : EuclideanSpace ℝ (Fin n)) :
        (χ (x + t • v) * H (x + t • v) - χ x * H x) ^ 2 ≤
          2 * e t x + (2 * B * t ^ 2) * q x := by
      let a : ℝ := χ (x + t • v) * (H (x + t • v) - H x)
      let b : ℝ := H x * (χ (x + t • v) - χ x)
      have ha : a ^ 2 ≤ e t x := by
        have hentry :=
          n11d3_entry_sq_le_total
            (FunctionalInequalities.Probability.Stein.hessianMatrix u (x + t • v) - FunctionalInequalities.Probability.Stein.hessianMatrix u x)
            (FunctionalInequalities.Probability.Stein.hessianMatrix u (x - t • v) - FunctionalInequalities.Probability.Stein.hessianMatrix u x) i j
        change (H (x + t • v) - H x) ^ 2 ≤ _ at hentry
        calc
          a ^ 2 =
              χ (x + t • v) ^ 2 * (H (x + t • v) - H x) ^ 2 := by
            dsimp only [a]
            ring
          _ ≤ (η x * Real.exp (-u x)) *
              ((∑ k, ∑ l,
                  (FunctionalInequalities.Probability.Stein.hessianMatrix u (x + t • v) - FunctionalInequalities.Probability.Stein.hessianMatrix u x) k l ^ 2) +
                ∑ k, ∑ l,
                  (FunctionalInequalities.Probability.Stein.hessianMatrix u (x - t • v) - FunctionalInequalities.Probability.Stein.hessianMatrix u x) k l ^ 2) :=
            mul_le_mul (henvelope t ht x) hentry (sq_nonneg _)
              (mul_nonneg (hη0 x) (Real.exp_pos _).le)
          _ = e t x := by
            dsimp only [e]
            ring
      have hb : b ^ 2 ≤ (B * t ^ 2) * q x := by
        by_cases hx : x ∈ tsupport η
        · have hqx : q x = 1 := Set.indicator_of_mem hx _
          rw [hqx, mul_one]
          have hH : H x ^ 2 ≤ (G : ℝ) ^ 2 := by
            have hh := pow_le_pow_left₀ (norm_nonneg (H x))
              (FunctionalInequalities.Probability.Stein.norm_hessianMatrix_entry_le_of_lipschitz_gradient_408915f hG x i j) 2
            simpa only [Real.norm_eq_abs, sq_abs] using hh
          have hcut :
              (χ (x + t • v) - χ x) ^ 2 ≤
                (L : ℝ) ^ 2 * t ^ 2 * ‖v‖ ^ 2 := by
            have hh := hL.norm_sub_le (x + t • v) x
            rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at hh
            have hs := pow_le_pow_left₀
              (norm_nonneg (χ (x + t • v) - χ x)) hh 2
            calc
              (χ (x + t • v) - χ x) ^ 2 =
                  ‖χ (x + t • v) - χ x‖ ^ 2 := by
                rw [Real.norm_eq_abs, sq_abs]
              _ ≤ ((L : ℝ) * (|t| * ‖v‖)) ^ 2 := hs
              _ = (L : ℝ) ^ 2 * t ^ 2 * ‖v‖ ^ 2 := by
                simp only [mul_pow, sq_abs]
                ring
          calc
            b ^ 2 = H x ^ 2 * (χ (x + t • v) - χ x) ^ 2 := by
              dsimp only [b]
              ring
            _ ≤ (G : ℝ) ^ 2 * ((L : ℝ) ^ 2 * t ^ 2 * ‖v‖ ^ 2) :=
              mul_le_mul hH hcut (sq_nonneg _) (sq_nonneg _)
            _ = B * t ^ 2 := by
              dsimp only [B]
              ring
        · have hqx : q x = 0 := Set.indicator_of_notMem hx _
          have hχt : χ (x + t • v) = 0 := hvanish t ht x hx
          have hχ0 : χ x = 0 := by
            simpa only [zero_smul, add_zero] using
              hvanish 0 (by norm_num) x hx
          have hb0 : b = 0 := by
            dsimp only [b]
            rw [hχt, hχ0]
            ring
          rw [hb0, hqx]
          norm_num
      have hsplit :
          χ (x + t • v) * H (x + t • v) - χ x * H x = a + b := by
        dsimp only [a, b]
        ring
      calc
        (χ (x + t • v) * H (x + t • v) - χ x * H x) ^ 2 =
            (a + b) ^ 2 := congrArg (fun z : ℝ => z ^ 2) hsplit
        _ ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
          nlinarith [sq_nonneg (a - b)]
        _ ≤ 2 * e t x + (2 * B * t ^ 2) * q x := by
          nlinarith [ha, hb]
    calc
      (∫ x, (χ (x + t • v) * FunctionalInequalities.Probability.Stein.hessianMatrix u (x + t • v) i j -
          χ x * FunctionalInequalities.Probability.Stein.hessianMatrix u x i j) ^ 2) ≤
          ∫ x, 2 * e t x + (2 * B * t ^ 2) * q x :=
        integral_mono hdiffint
          (((heint t).const_mul 2).add (hqint.const_mul (2 * B * t ^ 2)))
          hpoint
      _ = 2 * (∫ x, e t x) + (2 * B * t ^ 2) * J := by
        rw [integral_add ((heint t).const_mul 2)
          (hqint.const_mul (2 * B * t ^ 2)),
          integral_const_mul, integral_const_mul]
      _ ≤ 2 * (A * t ^ 2) + (2 * B * t ^ 2) * J := by
        have hscaled : 2 * (∫ x, e t x) ≤ 2 * (A * t ^ 2) :=
          mul_le_mul_of_nonneg_left (hebound t) (by norm_num : (0 : ℝ) ≤ 2)
        exact add_le_add hscaled (le_refl ((2 * B * t ^ 2) * J))
      _ = (2 * A + 2 * B * J) * t ^ 2 := by ring
