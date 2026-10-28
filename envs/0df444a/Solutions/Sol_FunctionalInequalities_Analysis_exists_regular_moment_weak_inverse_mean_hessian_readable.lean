-- Prove2me | solution 1 for FunctionalInequalities.Analysis.exists_regular_moment_weak_inverse_mean_hessian_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:32:58.956817+00:00
-- url     : https://prove2.me/submissions/e1adc7bb-a932-4f0d-b486-cb2d6960a4fd

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_WeakHessian
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Stein_HessianKernel
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Graph_Area
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_CEK_MomentRegularity_WeakHessian
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integral_inner_fderiv_gradient_tilted_eq_integral_fderiv_mul_readable
import Theorems.Thm_FunctionalInequalities_Analysis_exists_regular_moment_weak_first_derivative_readable
import Theorems.Thm_FunctionalInequalities_Analysis_hasWeakDerivAlong_inverse_hessian_of_logdet_readable
import Theorems.Thm_FunctionalInequalities_KLS_integral_fderiv_mul_fderiv_eq_inner_of_isotropic_map_readable
import Theorems.Thm_FunctionalInequalities_Probability_Stein_norm_hessianMatrix_entry_le_of_lipschitz_gradient_readable

section
open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
section WeakThirdDerivativeSymmetry
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open FunctionalInequalities.Probability.Stein
section StructuredSpace
variable {E : Type*}
variable [NormedAddCommGroup E]
section InnerProduct
variable [InnerProductSpace ℝ E]
private lemma FunctionalInequalities.Analysis.differentiableAt_fderiv_of_differentiableAt_gradient [CompleteSpace E]
    {u : E → ℝ} {x : E} (hx : DifferentiableAt ℝ (gradient u) x) :
    DifferentiableAt ℝ (fderiv ℝ u) x := by
  have heq :
      fderiv ℝ u = (InnerProductSpace.toDual ℝ E) ∘ gradient u := by
    funext y
    simp [gradient]
  rw [heq]
  exact
    (InnerProductSpace.toDual ℝ E).toContinuousLinearEquiv.differentiableAt.comp x hx
private lemma FunctionalInequalities.Analysis.hessian_coord_of_gradient_diff
    {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    {i j : Fin n} (hx : DifferentiableAt ℝ (gradient u) x) :
    fderiv ℝ (fun y => fderiv ℝ u y (EuclideanSpace.basisFun (Fin n) ℝ j)) x
        (EuclideanSpace.basisFun (Fin n) ℝ i) =
      hessianMatrix u x i j := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    differentiableAt_fderiv_of_differentiableAt_gradient hx
  have hc :
      DifferentiableAt ℝ
        (fun _ : EuclideanSpace ℝ (Fin n) =>
          EuclideanSpace.basisFun (Fin n) ℝ j) x :=
    (differentiable_const (EuclideanSpace.basisFun (Fin n) ℝ j) :
      Differentiable ℝ
        (fun _ : EuclideanSpace ℝ (Fin n) =>
          EuclideanSpace.basisFun (Fin n) ℝ j)).differentiableAt
  have h := fderiv_clm_apply hfd hc
  have h' := congrArg
    (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
      L (EuclideanSpace.basisFun (Fin n) ℝ i)) h
  simpa [hessianMatrix, bilinearIteratedFDerivTwo] using h'
private lemma FunctionalInequalities.Analysis.hessian_symm_of_gradient_diff
    {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    {i j : Fin n} (hu : ContDiff ℝ 1 u)
    (hx : DifferentiableAt ℝ (gradient u) x) :
    hessianMatrix u x i j = hessianMatrix u x j i := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    differentiableAt_fderiv_of_differentiableAt_gradient hx
  have hs :=
    second_derivative_symmetric
      (fun y => (hu.differentiable (by simp) y).hasFDerivAt)
      hfd.hasFDerivAt
      (EuclideanSpace.basisFun (Fin n) ℝ i)
      (EuclideanSpace.basisFun (Fin n) ℝ j)
  simpa [hessianMatrix, bilinearIteratedFDerivTwo] using hs
end InnerProduct
end StructuredSpace
end WeakThirdDerivativeSymmetry
section GradientDerivativeIdentification
open FunctionalInequalities.Analysis
section
private lemma FunctionalInequalities.Probability.Stein.hessianMatrix_entry_of_differentiableAt_gradient
    {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hu : ContDiff ℝ 1 u) (hx : DifferentiableAt ℝ (gradient u) x) (i j : Fin n) :
    hessianMatrix u x i j =
      ⟪EuclideanSpace.basisFun (Fin n) ℝ i,
        fderiv ℝ (gradient u) x (EuclideanSpace.basisFun (Fin n) ℝ j)⟫ := by
  rw [hessian_symm_of_gradient_diff hu hx,
    ← hessian_coord_of_gradient_diff hx]
  have heq :
      (fun y => fderiv ℝ u y (EuclideanSpace.basisFun (Fin n) ℝ i)) =
        fun y => ⟪gradient u y, EuclideanSpace.basisFun (Fin n) ℝ i⟫ := by
    funext y
    exact inner_gradient_left.symm
  rw [heq, fderiv_inner_apply ℝ hx
    (differentiableAt_const (EuclideanSpace.basisFun (Fin n) ℝ i))]
  simp [real_inner_comm]
/-- At a point where the gradient of a `C¹` potential is differentiable, its derivative
is represented by the coordinate Hessian. This pointwise bridge requires no `C²` hypothesis
and supports the weak regular moment-potential package for Letwin's Lemma 2.2. -/
theorem FunctionalInequalities.Probability.Stein.hessianMatrix_toEuclideanLin_of_differentiableAt_gradient
    {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hu : ContDiff ℝ 1 u) (hx : DifferentiableAt ℝ (gradient u) x) :
    Matrix.toEuclideanLin (hessianMatrix u x) =
      (fderiv ℝ (gradient u) x).toLinearMap := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  apply (LinearMap.toMatrix b.toBasis b.toBasis).injective
  rw [LinearMap.toMatrix_toLin]
  ext i j
  rw [LinearMap.toMatrix_apply,
    OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply]
  exact hessianMatrix_entry_of_differentiableAt_gradient hu hx i j
end
end GradientDerivativeIdentification
noncomputable section HessianEntryBounds
open FunctionalInequalities.Probability.Stein
open scoped RealInnerProductSpace
section
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
end HessianEntryBounds
end

section
open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
section
/-- If `(∇φ)_* ν = μ` and `μ` has finite second moment, then `∇φ ∈ L²(ν)`. -/
theorem FunctionalInequalities.Probability.Stein.memLp_two_gradient_of_map_eq {n : ℕ} {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ 1 φ)
    (ν μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hmap : (ν : Measure (EuclideanSpace ℝ (Fin n))).map (gradient φ) = (μ : Measure (EuclideanSpace ℝ (Fin n))))
    (hμ2 : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 (μ : Measure (EuclideanSpace ℝ (Fin n)))) :
    MemLp (gradient φ) 2 (ν : Measure (EuclideanSpace ℝ (Fin n))) := by
  have hg : Measurable (gradient φ) := (continuous_gradient hφ).measurable
  have hh : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 ((ν : Measure (EuclideanSpace ℝ (Fin n))).map (gradient φ)) := by
    rw [hmap]
    exact hμ2
  simpa only [Function.comp_def, id_eq] using
    (memLp_map_measure_iff continuous_id.aestronglyMeasurable hg.aemeasurable).mp hh
end
end

section
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace
section
universe u v
section Sandwich
variable {H : Type u} {V : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
omit [MeasurableSpace H] [BorelSpace H] in
theorem FunctionalInequalities.Analysis.continuous_gradient {g : H → ℝ} (hg : ContDiff ℝ 1 g) : Continuous (gradient g) := by
  have h1 : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  have h2 : (gradient g) = fun x => (InnerProductSpace.toDual ℝ H).symm (fderiv ℝ g x) := by
    funext x; rw [gradient]
  rw [h2]
  exact (InnerProductSpace.toDual ℝ H).symm.continuous.comp h1
end Sandwich
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
section RegularMomentWeakInverse
open scoped Matrix.Norms.Elementwise
section
include hn hκ hK hKc hKint hW hstrong hμ hiso in
/-- Actual regular-source weak inverse formula (Letwin (2.5)), retaining all R0/EX fields. -/
theorem FunctionalInequalities.Analysis.exists_regular_moment_weak_inverse :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L LF : NNReal)
        (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ContDiff ℝ 1 u ∧ LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
      LipschitzWith LF (fun x => -u x + W (gradient u x)) ∧
      (∀ x h, u (x + h) + u (x - h) - 2 * u x ≤ (4 / κ) * ‖h‖ ^ 2) ∧
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).PosDef ∧
        Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
        ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef) ∧
      (∀ k i j,
        HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
            MemLp (fun x => T x k i j) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      (∃ LE : NNReal,
        LipschitzWith LE (fun x => Real.exp (-u x + W (gradient u x)))) ∧
      (∀ k : Fin n,
        HasWeakDerivAlong (fun x => (hessianMatrix u x).det)
          (fun x => (hessianMatrix u x).det *
            ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => (hessianMatrix u x).det *
            ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
            2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        HasWeakDerivAlong (fun x => Real.log (hessianMatrix u x).det)
          (fun x => ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
            fderiv ℝ (fun y => -u y + W (gradient u y)) x
              (EuclideanSpace.basisFun (Fin n) ℝ k)) ∧
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
            -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ k) +
              ∑ a : Fin n, hessianMatrix u x k a *
                fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a))) ∧
      ∀ k i j : Fin n,
        HasWeakDerivAlong (fun x => (hessianMatrix u x)⁻¹ i j)
          (fun x => -(((hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j))
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => -(((hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j)) 2
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => (hessianMatrix u x)⁻¹ i j) (⊤ : ENNReal)
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  obtain ⟨u, L, LF, T, hc, hl, hnrm, hm, hC1, hG, hF, hw, hd, hT, he, hfirst⟩ :=
    exists_regular_moment_weak_first_derivative_readable hn hκ hK hKc hKint hW hstrong μ hμ hiso
  refine ⟨u, L, LF, T, hc, hl, hnrm, hm, hC1, hG, hF, hw, hd, hT, he, hfirst, ?_⟩
  exact hasWeakDerivAlong_inverse_hessian_of_logdet_readable hG hF
    (hd.mono fun _ hx => ⟨hx.1, hx.2.1⟩) hT
end
end RegularMomentWeakInverse
section RegularMomentWeakInverseMean
noncomputable section
open scoped ContDiff RealInnerProductSpace Topology
private lemma FunctionalInequalities.Analysis.mean_hessian_basis_entry {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    ⟪EuclideanSpace.basisFun (Fin n) ℝ i,
      Matrix.toEuclideanLin A (EuclideanSpace.basisFun (Fin n) ℝ j)⟫ = A i j := by
  rw [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_apply,
    EuclideanSpace.inner_single_left, Matrix.toLpLin_apply 2 2]
  simp [Matrix.mulVec, dotProduct]
include hn hκ hK hKc hKint hW hstrong hμ hiso in
theorem solution :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L LF : NNReal)
        (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
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
      ∀ i j : Fin n,
        Integrable (fun x => FunctionalInequalities.Probability.Stein.hessianMatrix u x i j)
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        (∫ x, FunctionalInequalities.Probability.Stein.hessianMatrix u x i j
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) =
          (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
  obtain ⟨u, L, LF, T, hc, hl, hnrm, hm, hC1, hG, hF, hw, hd, hT, he, hfirst, hInv⟩ :=
    FunctionalInequalities.Analysis.exists_regular_moment_weak_inverse hn hκ hK hKc hKint hW hstrong μ hμ hiso
  refine ⟨u, L, LF, T, hc, hl, hnrm, hm, hC1, hG, hF, hw, hd, hT, he, hfirst, hInv, ?_⟩
  have hexp : Integrable (fun x => Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    Integrable.of_integral_ne_zero (by rw [hnrm]; norm_num)
  let ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)) :=
    ⟨(volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u),
      isProbabilityMeasure_tilted hexp⟩
  have hgm : Measurable (gradient u) := (FunctionalInequalities.Analysis.continuous_gradient hC1).measurable
  have hmap : (ν : Measure (EuclideanSpace ℝ (Fin n))).map (gradient u) =
      (μ : Measure (EuclideanSpace ℝ (Fin n))) := hm
  have hmapProb : ν.map hgm.aemeasurable = μ := by
    apply Subtype.ext
    exact hmap
  have hIso : FunctionalInequalities.KLS.Isotropic (ν.map hgm.aemeasurable) := by
    rw [hmapProb]
    exact hiso
  have hgrad : MemLp (gradient u) 2
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) :=
    FunctionalInequalities.Probability.Stein.memLp_two_gradient_of_map_eq hC1 ν μ hmap hiso.memLp_two
  let e : Fin n → EuclideanSpace ℝ (Fin n) := EuclideanSpace.basisFun (Fin n) ℝ
  intro i j
  have hInt : Integrable (fun x => FunctionalInequalities.Probability.Stein.hessianMatrix u x i j)
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) := by
    change Integrable (fun x => FunctionalInequalities.Probability.Stein.hessianMatrix u x i j) (ν : Measure _)
    exact (integrable_const (16 / κ)).mono'
      (FunctionalInequalities.Probability.Stein.measurable_hessianMatrix_entry u i j).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        have hb := FunctionalInequalities.Probability.Stein.norm_hessianMatrix_entry_le_of_lipschitz_gradient_readable hG x i j
        have hk : 0 ≤ 16 / κ := by positivity
        simpa only [Real.coe_toNNReal _ hk] using hb)
  refine ⟨hInt, ?_⟩
  have hmean :=
    FunctionalInequalities.Analysis.BakryEmery.integral_inner_fderiv_gradient_tilted_eq_integral_fderiv_mul_readable
      u hC1 hG hc hexp hnrm hgrad (e j) (e i)
  have hsecond := FunctionalInequalities.KLS.integral_fderiv_mul_fderiv_eq_inner_of_isotropic_map_readable
    ν hgm hIso (e j) (e i)
  have heq : (fun x => FunctionalInequalities.Probability.Stein.hessianMatrix u x i j) =ᵐ[
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))]
      (fun x => ⟪fderiv ℝ (gradient u) x (e j), e i⟫) := by
    have had := (tilted_absolutelyContinuous
      (volume : Measure (EuclideanSpace ℝ (Fin n))) (-u)).ae_le
        (hG.ae_differentiableAt (μ := volume))
    filter_upwards [had] with x hx
    have hmat := FunctionalInequalities.Probability.Stein.hessianMatrix_toEuclideanLin_of_differentiableAt_gradient hC1 hx
    calc
      FunctionalInequalities.Probability.Stein.hessianMatrix u x i j =
          ⟪e i, Matrix.toEuclideanLin (FunctionalInequalities.Probability.Stein.hessianMatrix u x) (e j)⟫ :=
        (FunctionalInequalities.Analysis.mean_hessian_basis_entry (FunctionalInequalities.Probability.Stein.hessianMatrix u x) i j).symm
      _ = ⟪e i, fderiv ℝ (gradient u) x (e j)⟫ := by rw [hmat]; rfl
      _ = ⟪fderiv ℝ (gradient u) x (e j), e i⟫ := real_inner_comm _ _
  calc
    (∫ x, FunctionalInequalities.Probability.Stein.hessianMatrix u x i j
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) =
        ∫ x, ⟪fderiv ℝ (gradient u) x (e j), e i⟫
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) :=
      integral_congr_ae heq
    _ = ∫ x, fderiv ℝ u x (e j) * fderiv ℝ u x (e i)
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) := hmean
    _ = ⟪e j, e i⟫ := hsecond
    _ = (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
      change ⟪EuclideanSpace.basisFun (Fin n) ℝ j,
        EuclideanSpace.basisFun (Fin n) ℝ i⟫ = _
      rw [EuclideanSpace.inner_basisFun_real]
      simp [EuclideanSpace.basisFun_apply, Matrix.one_apply]
