-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.letwinQuadraticBound_of_tendsto_moments_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:48:25.718863+00:00
-- url     : https://prove2.me/submissions/2c9e6d33-d6e8-4802-9c8b-70feed5f1897

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments.Variance

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace ContDiff
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
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
section MomentLimit
open ProbabilityTheory Filter Topology
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
private lemma FunctionalInequalities.Analysis.BakryEmery.quadratic_basis_expansion
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (M : E →L[ℝ] E) (x : E) :
    ⟪M x, x⟫ =
      ∑ i, ∑ j, ⟪M (b i), b j⟫ * (⟪b i, x⟫ * ⟪b j, x⟫) := by
  classical
  calc
    ⟪M x, x⟫ =
        ⟪M (∑ i, ⟪b i, x⟫ • b i), ∑ j, ⟪b j, x⟫ • b j⟫ := by
      rw [b.sum_repr']
    _ = ∑ i, ∑ j, ⟪M (b i), b j⟫ * (⟪b i, x⟫ * ⟪b j, x⟫) := by
      rw [map_sum, sum_inner]
      simp only [map_smul, real_inner_smul_left, inner_sum, inner_smul_right]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
private lemma FunctionalInequalities.Analysis.BakryEmery.quadratic_coordinate_memLp
    [MeasurableSpace E] {ρ : Measure E} (hρ : MemLp id 4 ρ) (u v : E) :
    MemLp (fun x => ⟪u, x⟫ * ⟪v, x⟫) 2 ρ := by
  have ht : ENNReal.HolderTriple (4 : ENNReal) 4 2 := by
    constructor
    rw [← ENNReal.coe_ofNat 4, ← ENNReal.coe_ofNat 2,
      ← ENNReal.coe_inv (by norm_num : (4 : NNReal) ≠ 0),
      ← ENNReal.coe_inv (by norm_num : (2 : NNReal) ≠ 0),
      ← ENNReal.coe_add]
    norm_num
  have hu : MemLp (fun x => (⟪u, x⟫ : ℝ)) 4 ρ := hρ.const_inner u
  have hv : MemLp (fun x => (⟪v, x⟫ : ℝ)) 4 ρ := hρ.const_inner v
  exact hv.mul hu (hpqr := ht)
private lemma FunctionalInequalities.Analysis.BakryEmery.tendsto_integral_finite_linear_combination
    {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (μ : ℕ → Measure α) (ν : Measure α)
    (c : ι → ℝ) (f : ι → α → ℝ)
    (hμ : ∀ k i, Integrable (f i) (μ k))
    (hν : ∀ i, Integrable (f i) ν)
    (ht : ∀ i, Tendsto (fun k => ∫ x, f i x ∂μ k) atTop
      (𝓝 (∫ x, f i x ∂ν))) :
    Tendsto (fun k => ∫ x, ∑ i, c i * f i x ∂μ k) atTop
      (𝓝 (∫ x, ∑ i, c i * f i x ∂ν)) := by
  classical
  have heq :
      (fun k => ∫ x, ∑ i, c i * f i x ∂μ k) =
        (fun k => ∑ i, c i * ∫ x, f i x ∂μ k) := by
    funext k
    rw [integral_finsetSum _ (fun i _ => (hμ k i).const_mul (c i))]
    simp only [integral_const_mul]
  rw [heq, integral_finsetSum _ (fun i _ => (hν i).const_mul (c i))]
  simp only [integral_const_mul]
  exact tendsto_finsetSum _ (fun i _ => (ht i).const_mul (c i))
private lemma FunctionalInequalities.Analysis.BakryEmery.square_finite_linear_combination
    {α ι : Type*} [Fintype ι] (c : ι → ℝ) (f : ι → α → ℝ) :
    (fun x => (∑ i, c i * f i x) ^ 2) =
      (fun x => ∑ p : ι × ι, (c p.1 * c p.2) * (f p.1 x * f p.2 x)) := by
  classical
  funext x
  rw [pow_two, Finset.sum_mul_sum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.BakryEmery in
/-- **Letwin's quadratic bound passes to limits in the moments of degree ≤ 4** (Letwin
arXiv:2607.24164v1, Lemma A.1, last sentence: "both sides of (1.2) pass to the limit"): if
probability laws `μ k` with finite fourth moments satisfy `LetwinQuadraticBound` and all mixed
moments `∫ ∏ᵢ ⟪vᵢ, x⟫` of degree `d ≤ 4` converge to those of a law `ν` with finite fourth
moment, then `ν` satisfies `LetwinQuadraticBound`. -/
theorem solution [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (μ : ℕ → Measure E) (ν : Measure E) [∀ k, IsProbabilityMeasure (μ k)]
    [IsProbabilityMeasure ν] (hμ : ∀ k, MemLp id 4 (μ k)) (hν : MemLp id 4 ν)
    (hmom : ∀ d : ℕ, d ≤ 4 → ∀ v : Fin d → E,
      Tendsto (fun k => ∫ x, ∏ i, ⟪v i, x⟫ ∂(μ k)) atTop (𝓝 (∫ x, ∏ i, ⟪v i, x⟫ ∂ν)))
    (hL : ∀ k, FunctionalInequalities.Analysis.BakryEmery.LetwinQuadraticBound (μ k)) : FunctionalInequalities.Analysis.BakryEmery.LetwinQuadraticBound ν := by
  classical
  intro M hM
  let b := stdOrthonormalBasis ℝ E
  let I := Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
  let c : I → ℝ := fun p => ⟪M (b p.1), b p.2⟫
  let f : I → E → ℝ := fun p x => ⟪b p.1, x⟫ * ⟪b p.2, x⟫
  let Q : E → ℝ := fun x => ⟪M x, x⟫
  have hQ : Q = fun x => ∑ p : I, c p * f p x := by
    funext x
    dsimp only [Q, c, f]
    rw [Fintype.sum_prod_type]
    exact quadratic_basis_expansion b M x
  have hQsq :
      (fun x => Q x ^ 2) =
        (fun x => ∑ p : I × I,
          (c p.1 * c p.2) * (f p.1 x * f p.2 x)) := by
    rw [hQ]
    exact square_finite_linear_combination c f
  have hf (ρ : Measure E) (hρ : MemLp id 4 ρ) (p : I) :
      MemLp (f p) 2 ρ :=
    quadratic_coordinate_memLp hρ (b p.1) (b p.2)
  have hQQ (ρ : Measure E) (hρ : MemLp id 4 ρ) :
      MemLp Q 2 ρ := by
    rw [hQ]
    exact memLp_finsetSum _ (fun p _ => (hf ρ hρ p).const_mul (c p))
  have ht2 (p : I) :
      Tendsto (fun k => ∫ x, f p x ∂μ k) atTop (𝓝 (∫ x, f p x ∂ν)) := by
    simpa [f, Fin.prod_univ_two] using
      hmom 2 (by norm_num) ![b p.1, b p.2]
  have ht4 (p : I × I) :
      Tendsto (fun k => ∫ x, f p.1 x * f p.2 x ∂μ k) atTop
        (𝓝 (∫ x, f p.1 x * f p.2 x ∂ν)) := by
    simpa [f, Fin.prod_univ_four, mul_assoc] using
      hmom 4 (by norm_num) ![b p.1.1, b p.1.2, b p.2.1, b p.2.2]
  have hfirst :
      Tendsto (fun k => ∫ x, Q x ∂μ k) atTop (𝓝 (∫ x, Q x ∂ν)) := by
    rw [hQ]
    exact tendsto_integral_finite_linear_combination μ ν c f
      (fun k p => (hf (μ k) (hμ k) p).integrable (by norm_num))
      (fun p => (hf ν hν p).integrable (by norm_num)) ht2
  have hsecond :
      Tendsto (fun k => ∫ x, Q x ^ 2 ∂μ k) atTop
        (𝓝 (∫ x, Q x ^ 2 ∂ν)) := by
    rw [hQsq]
    exact tendsto_integral_finite_linear_combination μ ν
      (fun p : I × I => c p.1 * c p.2)
      (fun p : I × I => fun x => f p.1 x * f p.2 x)
      (fun k p => (hf (μ k) (hμ k) p.1).integrable_mul
        (hf (μ k) (hμ k) p.2))
      (fun p => (hf ν hν p.1).integrable_mul (hf ν hν p.2)) ht4
  have hv (ρ : Measure E) [IsProbabilityMeasure ρ] (hρ : MemLp id 4 ρ) :
      (∫ x, (Q x - ∫ y, Q y ∂ρ) ^ 2 ∂ρ) =
        (∫ x, Q x ^ 2 ∂ρ) - (∫ x, Q x ∂ρ) ^ 2 := by
    exact
      (ProbabilityTheory.variance_eq_integral (hQQ ρ hρ).aemeasurable).symm.trans
        (ProbabilityTheory.variance_eq_sub (hQQ ρ hρ))
  have hcenter :
      Tendsto (fun k => ∫ x, (Q x - ∫ y, Q y ∂μ k) ^ 2 ∂μ k) atTop
        (𝓝 (∫ x, (Q x - ∫ y, Q y ∂ν) ^ 2 ∂ν)) := by
    have heq :
        (fun k => ∫ x, (Q x - ∫ y, Q y ∂μ k) ^ 2 ∂μ k) =
          (fun k => (∫ x, Q x ^ 2 ∂μ k) - (∫ x, Q x ∂μ k) ^ 2) :=
      funext fun k => hv (μ k) (hμ k)
    rw [heq, hv ν hν]
    exact hsecond.sub (hfirst.pow 2)
  exact le_of_tendsto' hcenter (fun k => hL k M hM)
