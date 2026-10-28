-- Prove2me | solution 1 for FunctionalInequalities.Analysis.exists_regular_moment_weak_trace_energy_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:27:24.07456+00:00
-- url     : https://prove2.me/submissions/77b522cf-fbb2-4348-9797-bf4d70b32ea7

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_CEK_MomentRegularity_TraceStein
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_hessianMatrixIn_posSemidef_readable
import Theorems.Thm_FunctionalInequalities_Analysis_ae_weak_third_derivative_symm_readable
import Theorems.Thm_FunctionalInequalities_Analysis_four_tensor_trace_le_density_add_twice_energy_readable
import Theorems.Thm_FunctionalInequalities_Analysis_actual_source_weak_trace_conservativity_data_readable

section
noncomputable section
open MeasureTheory
open scoped ContDiff RealInnerProductSpace
section
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

section RegularSource
open MeasureTheory Set
open scoped ContDiff
variable {n : ℕ} (hn : 0 < n)
    {K : Set (EuclideanSpace ℝ (Fin n))} {W : EuclideanSpace ℝ (Fin n) → ℝ}
    {κ : ℝ} (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K)
    (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
    (hstrong : ConvexOn ℝ Set.univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
    (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ : (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) =
      (MeasureTheory.MeasureSpace.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hiso : FunctionalInequalities.KLS.Isotropic μ)
noncomputable section
open MeasureTheory Set Filter
open scoped RealInnerProductSpace ContDiff Topology
open FunctionalInequalities.Probability.Stein
section RegularMomentHalfDomination
open Matrix MeasureTheory
section
private theorem FunctionalInequalities.Analysis.integrable_and_integral_le_half_of_four_mul_le {α : Type*} [MeasurableSpace α]
    (mu : Measure α) (f g D : α → ℝ)
    (hf : Integrable f mu) (hg : Integrable g mu) (hD : AEStronglyMeasurable D mu)
    (hD0 : ∀ᵐ x ∂mu, 0 ≤ D x)
    (hUpper : ∀ᵐ x ∂mu, 4 * D x ≤ g x + 2 * f x)
    (hZero : (∫ x, g x ∂mu) = 0) :
    Integrable D mu ∧ (∫ x, D x ∂mu) ≤ (1 / 2 : ℝ) * ∫ x, f x ∂mu := by
  have hi : Integrable (fun x => g x + 2 * f x) mu := hg.add (hf.const_mul 2)
  have hInt : Integrable D mu := by
    apply (hi.norm.div_const 4).mono' hD
    filter_upwards [hD0, hUpper] with x hx0 hx
    rw [Real.norm_eq_abs, abs_of_nonneg hx0, Real.norm_eq_abs]
    have ha := le_abs_self (g x + 2 * f x)
    linarith
  refine ⟨hInt, ?_⟩
  have hm := integral_mono_ae (hInt.const_mul 4) hi hUpper
  rw [integral_const_mul, integral_add hg (hf.const_mul 2), integral_const_mul, hZero] at hm
  linarith
end
end RegularMomentHalfDomination
section RegularMomentWeakTraceEnergy
open MeasureTheory Filter Set Metric Matrix
open FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff Topology RealInnerProductSpace
include hn hκ hK hKc hKint hW hstrong hμ hiso in
set_option maxHeartbeats 1000000 in
/-- Weak half-trace tensor energy at one regular moment witness (Letwin arXiv:2607.24164v1 (2.14), weak form): with the
whole payload of the bounded weak cutoff testing, trace-quadratic testing, weak trace contraction and conservativity
retained at the same `u`, `L`, `LF`, `T`, for every positive semidefinite `B` the trace tensor energy
`D = ∑ (∇²u)⁻¹ᵢⱼ tr(B Tᵢ B Tⱼ)` is integrable for `e^{-u} dx` and `∫ D ≤ (1/2) ∫ tr(B ∇²u B ∇²u)`. -/
 theorem solution :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L LF : NNReal)
        (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      (      (      ((ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ContDiff ℝ 1 u ∧ LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
      LipschitzWith LF (fun x => -u x + W (gradient u x)) ∧
      (∀ x h, u (x + h) + u (x - h) - 2 * u x ≤ (4 / κ) * ‖h‖ ^ 2) ∧
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (FunctionalInequalities.Probability.Stein.hessianMatrix u x).PosDef ∧
        Real.log (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det = -u x + W (gradient u x) ∧
        ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) - FunctionalInequalities.Probability.Stein.hessianMatrix u x).PosSemidef) ∧
      (∀ k i j,
        FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => FunctionalInequalities.Probability.Stein.hessianMatrix u x i j) (fun x => T x k i j)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
            MemLp (fun x => T x k i j) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      (∃ LE : NNReal,
        LipschitzWith LE (fun x => Real.exp (-u x + W (gradient u x)))) ∧
      (∀ k : Fin n,
        FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det)
          (fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det *
            ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det *
            ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
            2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => Real.log (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det)
          (fun x => ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
            fderiv ℝ (fun y => -u y + W (gradient u y)) x
              (EuclideanSpace.basisFun (Fin n) ℝ k)) ∧
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
            -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ k) +
              ∑ a : Fin n, FunctionalInequalities.Probability.Stein.hessianMatrix u x k a *
                fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a))) ∧
      (∀ k i j : Fin n,
        FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j)
          (fun x => -(((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹) i j))
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => -(((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹) i j)) 2
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j) (⊤ : ENNReal)
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      (∀ i j : Fin n,
        Integrable (fun x => FunctionalInequalities.Probability.Stein.hessianMatrix u x i j)
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        (∫ x, FunctionalInequalities.Probability.Stein.hessianMatrix u x i j
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) =
          (1 : Matrix (Fin n) (Fin n) ℝ) i j) ∧
      (∀ i j : Fin n,
      FunctionalInequalities.Analysis.HasWeakDerivAlong
        (fun x => ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x i a b)).trace)
        (fun x => -FunctionalInequalities.Probability.Stein.hessianMatrix u x j i +
          ∑ a : Fin n,
            (T x j i a * fderiv ℝ W (gradient u x)
              (EuclideanSpace.basisFun (Fin n) ℝ a) +
            FunctionalInequalities.Probability.Stein.hessianMatrix u x i a *
              ∑ b : Fin n, FunctionalInequalities.Probability.Stein.hessianMatrix u x j b * FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x) b a))
        (EuclideanSpace.basisFun (Fin n) ℝ j) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp
          (fun x => -FunctionalInequalities.Probability.Stein.hessianMatrix u x j i +
            ∑ a : Fin n,
              (T x j i a * fderiv ℝ W (gradient u x)
                (EuclideanSpace.basisFun (Fin n) ℝ a) +
              FunctionalInequalities.Probability.Stein.hessianMatrix u x i a *
                ∑ b : Fin n, FunctionalInequalities.Probability.Stein.hessianMatrix u x j b * FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x) b a))
          2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
    (let Q := fun x i j => -FunctionalInequalities.Probability.Stein.hessianMatrix u x j i +
          ∑ a : Fin n,
            (T x j i a * fderiv ℝ W (gradient u x)
              (EuclideanSpace.basisFun (Fin n) ℝ a) +
            FunctionalInequalities.Probability.Stein.hessianMatrix u x i a *
              ∑ b : Fin n, FunctionalInequalities.Probability.Stein.hessianMatrix u x j b * FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x) b a)
    let R := fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹
    let D := fun x k b a => -((R x * (Matrix.of fun c d => T x k c d) * R x) b a)
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let C := fun x i j => Q x i j -
      (∑ a : Fin n, ∑ b : Fin n, T x i a b * D x j b a) +
      ∑ b : Fin n, T x b i j * (∑ a : Fin n, D x a b a)
    ∀ i j : Fin n,
      (∀ a : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => J x i j a) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      LocallyIntegrable (fun x => C x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        (∫ x, ∑ a : Fin n, J x i j a *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, C x i j * ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
  (    let R := fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let E := fun x i j => -FunctionalInequalities.Probability.Stein.hessianMatrix u x i j +
      (FunctionalInequalities.Probability.Stein.hessianMatrix u x * FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x) * FunctionalInequalities.Probability.Stein.hessianMatrix u x) i j +
      (R x * (Matrix.of fun a b => T x i a b) * R x *
        (Matrix.of fun a b => T x j a b)).trace
    ∀ i j : Fin n,
      (∀ a : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => J x i j a) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      LocallyIntegrable (fun x => E x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      LocallyIntegrable (fun x => Real.exp (-u x) * E x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        (∫ x, Real.exp (-u x) * (∑ a : Fin n, J x i j a *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, Real.exp (-u x) * E x i j * ψ x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
    let R := fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let E := fun x i j => -FunctionalInequalities.Probability.Stein.hessianMatrix u x i j +
      (FunctionalInequalities.Probability.Stein.hessianMatrix u x * FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x) * FunctionalInequalities.Probability.Stein.hessianMatrix u x) i j +
      (R x * (Matrix.of fun a b => T x i a b) * R x *
        (Matrix.of fun a b => T x j a b)).trace
    ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 ψ → HasCompactSupport ψ → ∀ l k i j : Fin n,
      (∀ b : Fin n, Integrable (fun x => Real.exp (-u x) * J x i j b * (ψ x * T x b l k + fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ b) * FunctionalInequalities.Probability.Stein.hessianMatrix u x l k))
        (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
      Integrable (fun x => Real.exp (-u x) * E x i j * (ψ x * FunctionalInequalities.Probability.Stein.hessianMatrix u x l k))
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      (∫ x, Real.exp (-u x) * (∑ b : Fin n, J x i j b * (ψ x * T x b l k + fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ b) * FunctionalInequalities.Probability.Stein.hessianMatrix u x l k))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, Real.exp (-u x) * E x i j * (ψ x * FunctionalInequalities.Probability.Stein.hessianMatrix u x l k)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
      ∃ c C : ℝ, 0 ≤ C ∧ (∀ x, 1 ≤ u x - c) ∧
      let χ := fun R x => Real.smoothTransition (2 - (u x - c) / R)
      let Lχ := fun R x => ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * FunctionalInequalities.Probability.Stein.hessianMatrix (χ R) x).trace -
        fderiv ℝ W (gradient u x) (gradient (χ R) x)
      (∀ R : ℝ, 1 ≤ R → ContDiff ℝ 1 (χ R) ∧ HasCompactSupport (χ R) ∧
        (∃ K : NNReal, LipschitzWith K (gradient (χ R))) ∧
        ∀ x, 0 ≤ χ R x ∧ χ R x ≤ 1) ∧
      (∀ x, MonotoneOn (fun R => χ R x) (Ici 1)) ∧
      (∀ x, Tendsto (fun R => χ R x) atTop (𝓝 1)) ∧
      (∀ R : ℝ, 1 ≤ R → Integrable (Lχ R)
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ∧
      (∀ R : ℝ, 1 ≤ R → (∫ x, |Lχ R x|
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ≤ C / R) ∧
      Tendsto (fun R : ℝ => ∫ x, |Lχ R x|
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) atTop (𝓝 0) ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ, ∃ C_B : ℝ, 0 ≤ C_B ∧
        (∀ x, ‖(B * FunctionalInequalities.Probability.Stein.hessianMatrix u x * B * FunctionalInequalities.Probability.Stein.hessianMatrix u x).trace‖ ≤ C_B) ∧
        LocallyIntegrable (fun x => (B * FunctionalInequalities.Probability.Stein.hessianMatrix u x * B * FunctionalInequalities.Probability.Stein.hessianMatrix u x).trace)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        (∀ k : Fin n,
          FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => (B * FunctionalInequalities.Probability.Stein.hessianMatrix u x * B * FunctionalInequalities.Probability.Stein.hessianMatrix u x).trace)
            (fun x => 2 * (B * FunctionalInequalities.Probability.Stein.hessianMatrix u x * B * (Matrix.of fun i j => T x k i j)).trace)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
            MemLp (fun x => 2 * (B * FunctionalInequalities.Probability.Stein.hessianMatrix u x * B * (Matrix.of fun i j => T x k i j)).trace)
              2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        ∀ r : ℝ, 1 ≤ r →
        Integrable (fun x => (B * FunctionalInequalities.Probability.Stein.hessianMatrix u x * B * FunctionalInequalities.Probability.Stein.hessianMatrix u x).trace * Lχ r x * Real.exp (-u x))
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        Integrable (fun x => (∑ i : Fin n, ∑ j : Fin n, (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j *
          (2 * (B * FunctionalInequalities.Probability.Stein.hessianMatrix u x * B * (Matrix.of fun a b => T x i a b)).trace) *
          fderiv ℝ (χ r) x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x))
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        (∫ x, (B * FunctionalInequalities.Probability.Stein.hessianMatrix u x * B * FunctionalInequalities.Probability.Stein.hessianMatrix u x).trace * Lχ r x * Real.exp (-u x)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, (∑ i : Fin n, ∑ j : Fin n, (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j *
          (2 * (B * FunctionalInequalities.Probability.Stein.hessianMatrix u x * B * (Matrix.of fun a b => T x i a b)).trace) *
          fderiv ℝ (χ r) x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ,
      let H := fun x => FunctionalInequalities.Probability.Stein.hessianMatrix u x
      let R := fun x => (H x)⁻¹
      let Tm := fun x i => Matrix.of fun a b => T x i a b
      let E := fun x => Matrix.of fun i j => -H x i j +
        (H x * FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x) * H x) i j +
        (R x * Tm x i * R x * Tm x j).trace
      let a := fun x i => 2 * (B * H x * B * Tm x i).trace
      let g := fun x => 2 * (B * H x * B * E x).trace +
        2 * ∑ i : Fin n, ∑ j : Fin n, R x i j * (B * Tm x i * B * Tm x j).trace
      LocallyIntegrable g (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        Integrable (fun x => Real.exp (-u x) * g x * ψ x)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        (∀ j : Fin n, Integrable (fun x => Real.exp (-u x) *
          (∑ i : Fin n, R x i j * a x i) *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ j))
          (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
        (∫ x, Real.exp (-u x) * (∑ j : Fin n, (∑ i : Fin n, R x i j * a x i) *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ j))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, Real.exp (-u x) * g x * ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ, B.PosSemidef →
      let H := fun x => FunctionalInequalities.Probability.Stein.hessianMatrix u x
      let R := fun x => (H x)⁻¹
      let Tm := fun x i => Matrix.of fun a b => T x i a b
      let E := fun x => Matrix.of fun i j => -H x i j +
        (H x * FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x) * H x) i j +
        (R x * Tm x i * R x * Tm x j).trace
      let g := fun x => 2 * (B * H x * B * E x).trace +
        2 * ∑ i : Fin n, ∑ j : Fin n, R x i j * (B * Tm x i * B * Tm x j).trace
      Integrable g ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        (∫ x, g x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) = 0) ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ, B.PosSemidef →
      let D := fun x => ∑ i : Fin n, ∑ j : Fin n, (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j *
        (B * (Matrix.of fun a b => T x i a b) * B * (Matrix.of fun a b => T x j a b)).trace
      Integrable D ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        (∫ x, D x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ≤
        (1 / 2 : ℝ) * ∫ x, (B * FunctionalInequalities.Probability.Stein.hessianMatrix u x * B * FunctionalInequalities.Probability.Stein.hessianMatrix u x).trace
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) := by
  obtain ⟨u, L, LF, T, hWhole, hConserve⟩ := FunctionalInequalities.Analysis.actual_source_weak_trace_conservativity_data_readable
    hn hκ hK hKc hKint hW hstrong μ hμ hiso
  have hcopy := hWhole.1
  rcases hcopy with ⟨hbase, hcutoffs⟩
  rcases hbase with ⟨_hc, _hl, hnrm, _hm, hC1, hG, _hF, _hw, hdata, hT, _he,
    _hfirst, hInv, _hmean, _hq, _hflux, _hweighted, _hbounded⟩
  obtain ⟨_c, _C, _hC, _hlower, _hreg, _hmono, _hpoint, _hint, _hbound, _hdecay, hrough⟩ := hcutoffs
  have hW2 : ContDiff ℝ 2 W := hW.of_le (WithTop.coe_le_coe.mpr le_top)
  have hVc : ConvexOn ℝ univ W := by
    have hn' : ConvexOn ℝ univ (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ^ 2) :=
      convexOn_univ_norm.pow (fun _ _ => norm_nonneg _) 2
    have hq := hn'.smul (show 0 ≤ κ / 2 by positivity)
    have he :
        (fun y => W y - κ / 2 * ‖y‖ ^ 2) +
          (fun y => (κ / 2) • ‖y‖ ^ 2) = W := by
      funext y
      simp only [Pi.add_apply, smul_eq_mul, sub_add_cancel]
    rw [← he]
    exact hstrong.add hq
  have hWP (x : EuclideanSpace ℝ (Fin n)) : (FunctionalInequalities.Probability.Stein.hessianMatrix W x).PosSemidef :=
    FunctionalInequalities.Analysis.BakryEmery.hessianMatrixIn_posSemidef_readable (EuclideanSpace.basisFun (Fin n) ℝ) hW2.contDiffAt
      (FunctionalInequalities.Analysis.BakryEmery.bilinearIteratedFDerivTwo_nonneg_of_convexOn hW2 hVc x)
  have hsym := FunctionalInequalities.Analysis.ae_weak_third_derivative_symm_readable hC1 hG (fun k i j => (hT k i j).1)
  have hRm (i j : Fin n) : AEMeasurable (fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have hLoc : LocallyIntegrable (fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      apply locallyIntegrable_iff.mpr
      intro S hS
      let : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
        isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
      exact ((hInv i i j).2.2 S hS).integrable (by simp)
    exact hLoc.aestronglyMeasurable.aemeasurable
  have hTm (k i j : Fin n) : AEMeasurable (fun x => T x k i j)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have hLoc : LocallyIntegrable (fun x => T x k i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      apply locallyIntegrable_iff.mpr
      intro S hS
      let : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
        isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
      exact ((hT k i j).2 S hS).integrable (by norm_num)
    exact hLoc.aestronglyMeasurable.aemeasurable
  have hexp := FunctionalInequalities.Analysis.BakryEmery.integrable_exp_neg_of_integral_eq_one
    (volume : Measure (EuclideanSpace ℝ (Fin n))) u hnrm
  let nu : Measure (EuclideanSpace ℝ (Fin n)) :=
    (volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)
  let : IsProbabilityMeasure nu := isProbabilityMeasure_tilted hexp
  have hac := tilted_absolutelyContinuous
    (volume : Measure (EuclideanSpace ℝ (Fin n))) (-u)
  refine ⟨u, L, LF, T, ⟨hWhole, hConserve⟩, ?_⟩
  intro B hB
  dsimp only
  let H := fun x => FunctionalInequalities.Probability.Stein.hessianMatrix u x
  let R := fun x => (H x)⁻¹
  let Tmat := fun x i => Matrix.of fun a b => T x i a b
  let E := fun x => Matrix.of fun i j => -H x i j +
    (H x * FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x) * H x) i j +
    (R x * Tmat x i * R x * Tmat x j).trace
  let f := fun x => (B * H x * B * H x).trace
  let g := fun x => 2 * (B * H x * B * E x).trace +
    2 * ∑ i : Fin n, ∑ j : Fin n, R x i j * (B * Tmat x i * B * Tmat x j).trace
  let D := fun x => ∑ i : Fin n, ∑ j : Fin n, R x i j * (B * Tmat x i * B * Tmat x j).trace
  obtain ⟨C_B, _hCB, hfbound, hfloc, _hweakB, _hpair⟩ := hrough B
  have hf : Integrable f nu :=
    (integrable_const C_B).mono' (hfloc.aestronglyMeasurable.mono_ac hac)
      (Filter.Eventually.of_forall hfbound)
  have hCons : Integrable g nu ∧ (∫ x, g x ∂nu) = 0 := hConserve B hB
  have hDvol : AEMeasurable D (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply Finset.aemeasurable_fun_sum
    intro i _
    apply Finset.aemeasurable_fun_sum
    intro j _
    apply (hRm i j).mul
    simp only [Tmat, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply]
    apply Finset.aemeasurable_fun_sum
    intro a _
    apply Finset.aemeasurable_fun_sum
    intro d _
    apply AEMeasurable.mul _ (hTm j d a)
    apply Finset.aemeasurable_fun_sum
    intro c _
    apply AEMeasurable.mul _ aemeasurable_const
    apply Finset.aemeasurable_fun_sum
    intro b _
    exact aemeasurable_const.mul (hTm i b c)
  have hBoth : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      0 ≤ D x ∧ 4 * D x ≤ g x + 2 * f x := by
    filter_upwards [hdata, hsym] with x hx hs
    exact FunctionalInequalities.Analysis.four_tensor_trace_le_density_add_twice_energy_readable B (H x)
      (FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x)) hB hx.1 (hWP _) (T x)
      (fun a b c => (hs a b c).1) (fun a b c => (hs a b c).2)
  exact FunctionalInequalities.Analysis.integrable_and_integral_le_half_of_four_mul_le nu f g D hf hCons.1
    (hDvol.aestronglyMeasurable.mono_ac hac)
    (hac.ae_le (hBoth.mono fun _ hx => hx.1))
    (hac.ae_le (hBoth.mono fun _ hx => hx.2)) hCons.2
