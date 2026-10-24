-- Prove2me | solution 1 for FunctionalInequalities.Analysis.integral_trace_quadratic_flux_eq_neg_density_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:46:21.05802+00:00
-- url     : https://prove2.me/submissions/62216da9-baa9-43e9-b5c5-6ee547dd0c7e

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_WeakDerivative_Basic
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity
import Mathlib.Topology.MetricSpace.Lipschitz
import Theorems.Thm_FunctionalInequalities_Analysis_integral_trace_contraction_of_coordinate_pairings_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_trace_mul_mul_mul_eq_sum_408915f

section
noncomputable section
open MeasureTheory
open scoped ContDiff
universe u
section SharedCompactLocalTools
open MeasureTheory Set Filter
open scoped ContDiff RealInnerProductSpace Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
/-- The product of two functions that are L2 on every compact set is locally integrable. -/
theorem FunctionalInequalities.Analysis.locallyIntegrable_mul_of_compact_L2 {n : ℕ}
    {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp f 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hg : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp g 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    LocallyIntegrable (fun x => f x * g x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  apply locallyIntegrable_iff.mpr
  intro S hS
  exact (hf S hS).integrable_mul (hg S hS)
/-- A function that is L2 on every compact set is locally integrable. -/
theorem FunctionalInequalities.Analysis.locallyIntegrable_of_compact_local_memLp_two {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp f 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    LocallyIntegrable f (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  apply locallyIntegrable_iff.mpr
  intro S hS
  let : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
    isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
  exact (hf S hS).integrable (by norm_num)
end
end
end SharedCompactLocalTools
end
end

noncomputable section
section WeakTraceLocalCoefficients
open MeasureTheory Filter Set Matrix
open scoped ContDiff Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
private theorem FunctionalInequalities.Analysis.trace_mul_sum_smul_slices {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ) :
    (A * (∑ i : Fin n, w i • T i)).trace =
      ∑ i : Fin n, w i * (A * T i).trace := by
  rw [Finset.mul_sum]
  simp only [mul_smul_comm, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
private theorem FunctionalInequalities.Analysis.trace_quadratic_flux_contraction {n : ℕ}
    (B H R : Matrix (Fin n) (Fin n) ℝ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (j : Fin n) :
    (∑ i : Fin n, R i j * (2 * (B * H * B * T i).trace)) =
      2 * (B * H * B * (∑ i : Fin n, R i j • T i)).trace := by
  rw [trace_mul_sum_smul_slices]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring
private theorem FunctionalInequalities.Analysis.trace_quadratic_tensor_flux_contraction {n : ℕ}
    (B R : Matrix (Fin n) (Fin n) ℝ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    (∑ j : Fin n, 2 * (B * T j * B * (∑ i : Fin n, R i j • T i)).trace) =
      2 * ∑ i : Fin n, ∑ j : Fin n, R i j * (B * T i * B * T j).trace := by
  classical
  calc
    _ = ∑ j : Fin n, ∑ i : Fin n, 2 * R i j * (B * T j * B * T i).trace := by
      apply Finset.sum_congr rfl
      intro j _
      rw [trace_mul_sum_smul_slices, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      have ht : (B * T j * B * T i).trace = (B * T i * B * T j).trace := by
        simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (B * T j) (B * T i)
      rw [ht]
      ring
private theorem FunctionalInequalities.Analysis.locallyIntegrable_mul_of_memLp_top {n : ℕ}
    {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : MemLp f (⊤ : ENNReal) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hg : LocallyIntegrable g (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    LocallyIntegrable (fun x => f x * g x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  apply locallyIntegrable_iff.mpr
  intro S hS
  have hg1 : MemLp g 1 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
    memLp_one_iff_integrable.mpr (locallyIntegrable_iff.mp hg S hS)
  exact memLp_one_iff_integrable.mp (hg1.mul' (hf.restrict S))
private theorem FunctionalInequalities.Analysis.locallyIntegrable_trace_four_of_entry_products {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ)
    (F G : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    (hFG : ∀ i j k l : Fin n,
      LocallyIntegrable (fun x => F x i j * G x k l)
        (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    LocallyIntegrable (fun x => (A * F x * B * G x).trace)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  classical
  let c := fun q : Fin n × Fin n × Fin n × Fin n => A q.1 q.2.1 * B q.2.2.1 q.2.2.2
  apply locallyIntegrable_iff.mpr
  intro S hS
  have hsum : IntegrableOn (fun x => ∑ q : Fin n × Fin n × Fin n × Fin n,
      c q * (F x q.2.1 q.2.2.1 * G x q.2.2.2 q.1)) S
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply integrable_finsetSum
    intro q _
    exact ((hFG q.2.1 q.2.2.1 q.2.2.2 q.1).integrableOn_isCompact hS).const_mul (c q)
  convert hsum using 1
  funext x
  exact trace_mul_mul_mul_eq_sum_408915f A (F x) B (G x)
private theorem FunctionalInequalities.Analysis.trace_quadratic_contraction_local_coefficients {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ)
    (H E : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    (T J : EuclideanSpace ℝ (Fin n) → Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hH : ∀ i j : Fin n, MemLp (fun x => H x i j) (⊤ : ENNReal)
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hT : ∀ a i j : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => T x a i j) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hJ : ∀ a i j : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => J x a i j) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hE : ∀ i j : Fin n, LocallyIntegrable (fun x => E x i j)
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    LocallyIntegrable (fun x => (B * H x * B * E x).trace)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    (∀ a : Fin n,
      LocallyIntegrable (fun x => (B * T x a * B * J x a).trace)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      LocallyIntegrable (fun x => (B * H x * B * J x a).trace)
        (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
    (∀ a l k i j : Fin n,
      LocallyIntegrable (fun x => T x a l k * J x a i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
    (∀ a l k i j : Fin n,
      LocallyIntegrable (fun x => H x l k * J x a i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
    (∀ l k i j : Fin n,
      LocallyIntegrable (fun x => H x l k * E x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
  have hJT (a l k i j : Fin n) := locallyIntegrable_mul_of_compact_L2
    (hT a l k) (hJ a i j)
  have hHJ (a l k i j : Fin n) := locallyIntegrable_mul_of_memLp_top
    (hH l k) (locallyIntegrable_of_compact_local_memLp_two (hJ a i j))
  have hHE (l k i j : Fin n) := locallyIntegrable_mul_of_memLp_top (hH l k) (hE i j)
  refine ⟨locallyIntegrable_trace_four_of_entry_products B B H E hHE, ?_, hJT, hHJ, hHE⟩
  intro a
  exact ⟨locallyIntegrable_trace_four_of_entry_products B B (fun x => T x a)
      (fun x => J x a) (hJT a),
    locallyIntegrable_trace_four_of_entry_products B B H (fun x => J x a) (hHJ a)⟩
end
end
end WeakTraceLocalCoefficients
section WeakTraceIdentity
open MeasureTheory Filter Set Matrix
open scoped ContDiff Topology
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
set_option maxHeartbeats 1000000 in
/-- Weak trace contraction of a tested Hessian-type flux identity (Letwin arXiv:2607.24164v1, weak counterpart of
Lemma 2.4 (2.8)/(2.10)): for rough matrix fields `H`, `R`, `E`, a tensor field `T` and a weight `ρ` with the stated
compact-local integrability, weak derivatives and tested identities, the contracted trace flux against every compact
C1 test equals minus the contracted density. All finite dimensions, every constant matrix `B`. -/
theorem solution {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ)
    (H R E : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    (T : EuclideanSpace ℝ (Fin n) → Fin n → Matrix (Fin n) (Fin n) ℝ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hρ : Continuous ρ)
    (hH : ∀ i j : Fin n, MemLp (fun x => H x i j) (⊤ : ENNReal)
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hT : ∀ a i j : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => T x a i j) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hJ : ∀ i j a : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => ∑ b : Fin n, R x b a * T x b i j) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hE : ∀ i j : Fin n, LocallyIntegrable (fun x => E x i j)
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hTest : ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 ψ → HasCompactSupport ψ → ∀ l k i j : Fin n,
      (∫ x, ρ x * (∑ a : Fin n, (∑ b : Fin n, R x b a * T x b i j) *
        (ψ x * T x a l k +
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a) * H x l k))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, ρ x * E x i j * (ψ x * H x l k)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) :
    let a := fun x i => 2 * (B * H x * B * T x i).trace
    let g := fun x => 2 * (B * H x * B * E x).trace +
      2 * ∑ i : Fin n, ∑ j : Fin n, R x i j * (B * T x i * B * T x j).trace
    LocallyIntegrable g (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      Integrable (fun x => ρ x * g x * ψ x)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      (∀ j : Fin n, Integrable (fun x => ρ x *
        (∑ i : Fin n, R x i j * a x i) *
        fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ j))
        (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
      (∫ x, ρ x * (∑ j : Fin n, (∑ i : Fin n, R x i j * a x i) *
        fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ j))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, ρ x * g x * ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
  classical
  let Jn := fun x a => ∑ b : Fin n, R x b a • T x b
  have hJn (a i j : Fin n) (S : Set (EuclideanSpace ℝ (Fin n))) (hS : IsCompact S) :
      MemLp (fun x => Jn x a i j) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
    simpa only [Jn, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] using hJ i j a S hS
  obtain ⟨hFE, hQF, hJT, hHJ, hHE⟩ :=
    trace_quadratic_contraction_local_coefficients B H E T Jn hH hT hJn hE
  let g := fun x => 2 * (B * H x * B * E x).trace +
    2 * ∑ i : Fin n, ∑ j : Fin n, R x i j * (B * T x i * B * T x j).trace
  let gJ := fun x => 2 * (B * H x * B * E x).trace +
    ∑ a : Fin n, 2 * (B * T x a * B * Jn x a).trace
  have hgJ : LocallyIntegrable gJ (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply locallyIntegrable_iff.mpr
    intro S hS
    exact ((hFE.integrableOn_isCompact hS).const_mul 2).add
      (integrable_finsetSum Finset.univ fun a _ =>
        ((hQF a).1.integrableOn_isCompact hS).const_mul 2)
  have hgEq : g = gJ := by
    funext x
    dsimp only [g, gJ, Jn]
    rw [trace_quadratic_tensor_flux_contraction]
  have hgApply (x) : g x = gJ x := congrFun hgEq x
  have hg : LocallyIntegrable g (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    rw [hgEq]
    exact hgJ
  refine ⟨hg, ?_⟩
  intro psi hpsi hcpsi
  let dpsi := fun a x => fderiv ℝ psi x (EuclideanSpace.basisFun (Fin n) ℝ a)
  have hdpsi (a : Fin n) : Continuous (dpsi a) :=
    (hpsi.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hcdpsi (a : Fin n) : HasCompactSupport (dpsi a) :=
    hcpsi.fderiv_apply ℝ (EuclideanSpace.basisFun (Fin n) ℝ a)
  have hwpsi : Continuous (fun x => ρ x * psi x) := hρ.mul hpsi.continuous
  have hcwpsi : HasCompactSupport (fun x => ρ x * psi x) := hcpsi.mul_left
  have hwdpsi (a : Fin n) : Continuous (fun x => ρ x * dpsi a x) := hρ.mul (hdpsi a)
  have hcwdpsi (a : Fin n) : HasCompactSupport (fun x => ρ x * dpsi a x) :=
    (hcdpsi a).mul_left
  have hweight {f w : EuclideanSpace ℝ (Fin n) → ℝ}
      (hf : LocallyIntegrable f (volume : Measure (EuclideanSpace ℝ (Fin n))))
      (hw : Continuous w) (hcw : HasCompactSupport w) :
      Integrable (fun x => w x * f x) (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    simpa only [smul_eq_mul] using hf.integrable_smul_left_of_hasCompactSupport hw hcw
  have hTensor (a : Fin n) : Integrable
      (fun x => ρ x * psi x * (2 * (B * T x a * B * Jn x a).trace))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have hh := (hweight (hQF a).1 hwpsi hcwpsi).const_mul 2
    apply hh.congr
    filter_upwards [] with x
    ring
  have hFlux (a : Fin n) : Integrable
      (fun x => ρ x * dpsi a x * (2 * (B * H x * B * Jn x a).trace))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have hh := (hweight (hQF a).2 (hwdpsi a) (hcwdpsi a)).const_mul 2
    apply hh.congr
    filter_upwards [] with x
    ring
  have hTraceForce : Integrable
      (fun x => ρ x * psi x * (2 * (B * H x * B * E x).trace))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have hh := (hweight hFE hwpsi hcwpsi).const_mul 2
    apply hh.congr
    filter_upwards [] with x
    ring
  have hPair (l k i j : Fin n) : Integrable (fun x => ρ x *
      (∑ a : Fin n, Jn x a i j * (psi x * T x a l k + dpsi a x * H x l k)))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have hh := integrable_finsetSum Finset.univ fun a _ =>
      (hweight (hJT a l k i j) hwpsi hcwpsi).add
        (hweight (hHJ a l k i j) (hwdpsi a) (hcwdpsi a))
    apply hh.congr
    filter_upwards [] with x
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    simp only [Pi.add_apply]
    ring
  have hForce (l k i j : Fin n) : Integrable
      (fun x => ρ x * E x i j * (psi x * H x l k))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply (hweight (hHE l k i j) hwpsi hcwpsi).congr
    filter_upwards [] with x
    ring
  have hTestJn (l k i j : Fin n) :
      (∫ x, ρ x * (∑ a : Fin n, Jn x a i j *
        (psi x * T x a l k + dpsi a x * H x l k))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, ρ x * E x i j * (psi x * H x l k)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
    simpa only [Jn, dpsi, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] using
      hTest psi hpsi hcpsi l k i j
  have hID := FunctionalInequalities.Analysis.integral_trace_contraction_of_coordinate_pairings_408915f
    (volume : Measure (EuclideanSpace ℝ (Fin n))) B H E T Jn ρ psi dpsi
    hPair hForce hTensor hFlux hTraceForce hTestJn
  have hfluxEq (a : Fin n) (x) :
      (∑ i : Fin n, R x i a * (2 * (B * H x * B * T x i).trace)) =
      2 * (B * H x * B * Jn x a).trace :=
    trace_quadratic_flux_contraction B (H x) (R x) (T x) a
  refine ⟨?_, ?_, ?_⟩
  · have hh := hweight hgJ hwpsi hcwpsi
    apply hh.congr
    filter_upwards [] with x
    rw [← hgApply x]
    ring
  · intro a
    apply (hFlux a).congr
    filter_upwards [] with x
    rw [hfluxEq a x]
    ring
  · change (∫ x, ρ x * (∑ a : Fin n,
      (∑ i : Fin n, R x i a * (2 * (B * H x * B * T x i).trace)) * dpsi a x)
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, ρ x * g x * psi x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
    simpa only [hfluxEq, hgApply] using hID
