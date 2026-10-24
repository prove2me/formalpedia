-- Prove2me | solution 1 for FunctionalInequalities.Analysis.posDef_and_det_eq_of_quadratic_expansion_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:27:55.993149+00:00
-- url     : https://prove2.me/submissions/4edfcb2f-b197-4a9f-a444-334ff46ad4d0

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
import Theorems.Thm_FunctionalInequalities_Analysis_det_hessianMatrix_le_of_lower_touch_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_hessianMatrix_quadraticAt_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_le_det_hessianMatrix_of_upper_touch_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_posSemidef_hessianMatrix_of_upper_touch_408915f

noncomputable section
open Set Metric Filter
open scoped RealInnerProductSpace Topology
open FunctionalInequalities.Probability.Stein
section LT12E1AlexandrovPointEquation
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
/-- `quadraticAt A x₀ b c` is smooth (weak Letwin route). -/
theorem FunctionalInequalities.Analysis.contDiff_quadraticAt {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x₀ b : EuclideanSpace ℝ (Fin n))
    (c : ℝ) : ContDiff ℝ 2 (quadraticAt A x₀ b c) := by
  let T := (Matrix.toEuclideanLin A).toContinuousLinearMap
  change ContDiff ℝ 2
    (fun x => c + ⟪b, x - x₀⟫ + (1 / 2 : ℝ) * ⟪x - x₀, T (x - x₀)⟫)
  exact (contDiff_const.add
    (contDiff_const.inner ℝ (contDiff_id.sub contDiff_const))).add
    (contDiff_const.mul ((contDiff_id.sub contDiff_const).inner ℝ
      (T.contDiff.comp (contDiff_id.sub contDiff_const))))
private lemma FunctionalInequalities.Analysis.quadraticAt_shift {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (x₀ b : EuclideanSpace ℝ (Fin n))
    (c : ℝ) (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    quadraticAt (A + t • 1) x₀ b c x =
      quadraticAt A x₀ b c x + t / 2 * ‖x - x₀‖ ^ 2 := by
  unfold quadraticAt
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    inner_add_right, inner_smul_right]
  rw [show Matrix.toEuclideanLin (1 : Matrix (Fin n) (Fin n) ℝ) =
    LinearMap.id by exact Matrix.toLpLin_one 2]
  simp only [LinearMap.id_apply, real_inner_self_eq_norm_sq]
  ring
private lemma FunctionalInequalities.Analysis.quadraticAt_shift_sub {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (x₀ b : EuclideanSpace ℝ (Fin n))
    (c : ℝ) (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    quadraticAt (A - t • 1) x₀ b c x =
      quadraticAt A x₀ b c x - t / 2 * ‖x - x₀‖ ^ 2 := by
  simpa only [neg_smul, sub_eq_add_neg, neg_div, neg_mul] using
    quadraticAt_shift A x₀ b c x (-t)
private lemma FunctionalInequalities.Analysis.posSemidef_of_positive_shifts {n : ℕ}
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsHermitian)
    (hu : ∀ t : ℝ, 0 < t → (B + t • 1).PosSemidef) : B.PosSemidef := by
  have hc : Continuous (fun t : ℝ => B + t • 1) :=
    continuous_const.add (continuous_id.smul continuous_const)
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨hB, ?_⟩
  intro v
  have hv : Continuous (fun t : ℝ => star v ⬝ᵥ (B + t • 1).mulVec v) :=
    continuous_const.dotProduct (hc.matrix_mulVec continuous_const)
  have hh : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 ≤ star v ⬝ᵥ (B + t • 1).mulVec v := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hu t ht).dotProduct_mulVec_nonneg v
  simpa using ge_of_tendsto
    (hv.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Ioi 0))) hh
private lemma FunctionalInequalities.Analysis.posSemidef_sub_eventually {n : ℕ}
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.PosDef) :
    ∀ᶠ t : ℝ in 𝓝 0, (B - t • 1).PosSemidef := by
  have he : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, t < hB.1.eigenvalues i :=
    eventually_all.mpr (fun i => eventually_lt_nhds (hB.eigenvalues_pos i))
  filter_upwards [he] with t ht
  let U := Unitary.conjStarAlgAut ℝ (Matrix (Fin n) (Fin n) ℝ)
    hB.1.eigenvectorUnitary
  have hd : (Matrix.diagonal (fun i => hB.1.eigenvalues i - t)).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun i => le_of_lt (sub_pos.mpr (ht i)))
  have hc : Matrix.diagonal (fun _ : Fin n => t) =
      t • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal, h]
  have heq : B - t • 1 =
      U (Matrix.diagonal (fun i => hB.1.eigenvalues i - t)) := by
    rw [← Matrix.diagonal_sub, map_sub, hc, map_smul, map_one]
    congr 1
    simpa [U, Function.comp_def] using hB.1.spectral_theorem
  rw [heq]
  exact hd.mul_mul_conjTranspose_same _
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- **The Monge–Ampère equation at points of second-order differentiability** (weak Letwin route): if the subgradient images of the convex `u` on open subsets of `Ω` carry the density `f`,
`f` is continuous and positive at `x₀ ∈ Ω`, and `u` has a second-order expansion at `x₀` with a symmetric
matrix `B` (`|u x − (u x₀ + ⟪g, x − x₀⟫ + ½ ⟪x − x₀, B (x − x₀)⟫)| ≤ ε ‖x − x₀‖²` near `x₀` for every
`ε > 0`), then `B` is positive definite and `det B = f x₀`. -/
theorem solution {n : ℕ} {u f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hconv : ConvexOn ℝ univ u) {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω)
    (hMA : ∀ G : Set (EuclideanSpace ℝ (Fin n)), IsOpen G → G ⊆ Ω →
      (volume : Measure (EuclideanSpace ℝ (Fin n))) (FunctionalInequalities.Analysis.subgradientImage u G) =
        ∫⁻ x in G, ENNReal.ofReal (f x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
    {x₀ : EuclideanSpace ℝ (Fin n)} (hx₀ : x₀ ∈ Ω) (hf : ContinuousAt f x₀) (hfpos : 0 < f x₀)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsHermitian) {g : EuclideanSpace ℝ (Fin n)}
    (hexp : ∀ ε > 0, ∀ᶠ x in 𝓝 x₀, |u x - FunctionalInequalities.Analysis.quadraticAt B x₀ g (u x₀) x| ≤ ε * ‖x - x₀‖ ^ 2) :
    B.PosDef ∧ B.det = f x₀ := by
  have hu : ∀ t : ℝ, 0 < t →
      (B + t • 1).PosSemidef ∧ f x₀ ≤ (B + t • 1).det := by
    intro t ht
    have hs : (B + t • 1).IsHermitian :=
      hB.add (Matrix.isHermitian_one.smul (IsSelfAdjoint.all t))
    have hc : u x₀ = FunctionalInequalities.Analysis.quadraticAt (B + t • 1) x₀ g (u x₀) x₀ := by
      simp [FunctionalInequalities.Analysis.quadraticAt]
    have htouch : ∀ᶠ x in 𝓝 x₀, u x ≤ FunctionalInequalities.Analysis.quadraticAt (B + t • 1) x₀ g (u x₀) x := by
      filter_upwards [hexp (t / 2) (by positivity)] with x hx
      rw [quadraticAt_shift]
      have hh := (abs_le.mp hx).2
      linarith
    have hψ : ContDiffAt ℝ 2 (FunctionalInequalities.Analysis.quadraticAt (B + t • 1) x₀ g (u x₀)) x₀ :=
      (FunctionalInequalities.Analysis.contDiff_quadraticAt (B + t • 1) x₀ g (u x₀)).contDiffAt
    have hp := FunctionalInequalities.Analysis.posSemidef_hessianMatrix_of_upper_touch_408915f hconv hψ hc htouch
    have hd := FunctionalInequalities.Analysis.le_det_hessianMatrix_of_upper_touch_408915f hconv hΩ hMA hx₀ hf hψ hc htouch
    rw [FunctionalInequalities.Analysis.hessianMatrix_quadraticAt_408915f hs] at hp hd
    exact ⟨hp, hd⟩
  have hplus : Continuous (fun t : ℝ => B + t • 1) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hdet_lower : f x₀ ≤ B.det := by
    have hh : ∀ᶠ t : ℝ in 𝓝[>] 0, f x₀ ≤ (B + t • 1).det := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact (hu t ht).2
    simpa using ge_of_tendsto
      (hplus.matrix_det.continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Ioi 0))) hh
  have hps : B.PosSemidef :=
    posSemidef_of_positive_shifts hB (fun t ht => (hu t ht).1)
  have hpd : B.PosDef :=
    hps.posDef_iff_det_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le hfpos hdet_lower))
  refine ⟨hpd, le_antisymm ?_ hdet_lower⟩
  have hlower : ∀ᶠ t : ℝ in 𝓝[>] 0, (B - t • 1).det ≤ f x₀ := by
    have he : ∀ᶠ t : ℝ in 𝓝[>] 0, (B - t • 1).PosSemidef :=
      (posSemidef_sub_eventually hpd).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, he] with t ht hpt
    have hc : u x₀ = FunctionalInequalities.Analysis.quadraticAt (B - t • 1) x₀ g (u x₀) x₀ := by
      simp [FunctionalInequalities.Analysis.quadraticAt]
    have htouch : ∀ᶠ x in 𝓝 x₀, FunctionalInequalities.Analysis.quadraticAt (B - t • 1) x₀ g (u x₀) x ≤ u x := by
      filter_upwards [hexp (t / 2) (by exact div_pos ht (by norm_num))] with x hx
      rw [quadraticAt_shift_sub]
      have hh := (abs_le.mp hx).1
      linarith
    have hψ : ContDiffAt ℝ 2 (FunctionalInequalities.Analysis.quadraticAt (B - t • 1) x₀ g (u x₀)) x₀ :=
      (FunctionalInequalities.Analysis.contDiff_quadraticAt (B - t • 1) x₀ g (u x₀)).contDiffAt
    have hH : (FunctionalInequalities.Probability.Stein.hessianMatrix (FunctionalInequalities.Analysis.quadraticAt (B - t • 1) x₀ g (u x₀)) x₀).PosSemidef := by
      rw [FunctionalInequalities.Analysis.hessianMatrix_quadraticAt_408915f hpt.1]
      exact hpt
    have hd := FunctionalInequalities.Analysis.det_hessianMatrix_le_of_lower_touch_408915f
      hconv hΩ hMA hx₀ hf hfpos.le hψ hH hc htouch
    rwa [FunctionalInequalities.Analysis.hessianMatrix_quadraticAt_408915f hpt.1] at hd
  have hminus : Continuous (fun t : ℝ => B - t • 1) :=
    continuous_const.sub (continuous_id.smul continuous_const)
  simpa using le_of_tendsto
    (hminus.matrix_det.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Ioi 0))) hlower
