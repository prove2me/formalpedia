-- Prove2me | solution 1 for FunctionalInequalities.Analysis.hasWeakDerivAlong_mongeAmpere_first_rhs_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:39:24.441026+00:00
-- url     : https://prove2.me/submissions/e13e9443-40cd-41e0-8645-6942d8e78572

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Calculus
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_WeakHessian
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_WeakHessianEvolution
import Theorems.Thm_FunctionalInequalities_Analysis_HasWeakDerivAlong_congr_ae_readable
import Theorems.Thm_FunctionalInequalities_Analysis_HasWeakDerivAlong_mul_of_locally_bounded_readable
import Theorems.Thm_FunctionalInequalities_Analysis_exists_lipschitzWith_weak_fderiv_comp_gradient_readable
import Theorems.Thm_FunctionalInequalities_Analysis_hasWeakDerivAlong_finsetSum_mul_readable
import Theorems.Thm_FunctionalInequalities_Analysis_hasWeakDerivAlong_of_lipschitz_readable
import Theorems.Thm_FunctionalInequalities_Probability_Stein_norm_hessianMatrix_entry_le_of_lipschitz_gradient_readable

section
noncomputable section
open MeasureTheory
open scoped ContDiff
universe u
section SharedCompactLocalTools
open MeasureTheory Set Filter
open scoped ContDiff RealInnerProductSpace Topology
section
/-- A continuous function is essentially bounded on every compact set. -/
theorem FunctionalInequalities.Analysis.memLp_top_restrict_of_continuous {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Continuous f)
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : IsCompact S) :
    MemLp f (⊤ : ENNReal) ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  let : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
    isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hf.continuousOn
  apply MemLp.of_bound hf.measurable.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem hS.measurableSet] with x hx
  exact hC x hx
end
end SharedCompactLocalTools
end
end

section
open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
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
noncomputable section
open MeasureTheory Set
open scoped Topology ContDiff
section
/-- The total coordinate Hessian entry is L2 on every compact set, from the
actual Lipschitz-gradient bound. No differentiability or PDE premise is added. -/
theorem FunctionalInequalities.Probability.Stein.memLp_hessianMatrix_entry_of_isCompact {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {G : NNReal}
    (hG : LipschitzWith G (gradient u)) (i j : Fin n)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : IsCompact S) :
    MemLp (fun x => hessianMatrix u x i j) 2
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  let : IsFiniteMeasure
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
    isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
  exact MemLp.of_bound
    (measurable_hessianMatrix_entry u i j).aestronglyMeasurable
    (G : ℝ)
    (Filter.Eventually.of_forall fun x =>
      norm_hessianMatrix_entry_le_of_lipschitz_gradient_readable hG x i j)
end
end
end

noncomputable section
section MongeAmpereFirstRhsDerivative
open MeasureTheory Set Filter
open FunctionalInequalities.Probability.Stein
open FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace Topology
private lemma FunctionalInequalities.Analysis.differentiableAt_fderiv_of_differentiableAt_gradient
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
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
/-- Closed weak-coordinate calculation already used inside the canonical
weak third-derivative symmetry proof; kept private for its consuming module. -/
private theorem FunctionalInequalities.Analysis.hasWeakDerivAlong_fderiv_of_lipschitz_gradient {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {G : NNReal}
    (hGradLip : LipschitzWith G (gradient u)) (i j : Fin n) :
    HasWeakDerivAlong
      (fun x => fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i))
      (fun x => hessianMatrix u x j i) (EuclideanSpace.basisFun (Fin n) ℝ j) ∧
    ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => hessianMatrix u x j i) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  have hCoordLip : LipschitzWith (‖(innerSL ℝ) (e i)‖₊ * G)
      (fun x => fderiv ℝ u x (e i)) := by
    simpa [Function.comp_def, inner_gradient_left] using
      (((innerSL ℝ) (e i)).lipschitz.comp hGradLip)
  have hAE : (fun x => fderiv ℝ (fun y => fderiv ℝ u y (e i)) x (e j)) =ᵐ[
      (volume : Measure (EuclideanSpace ℝ (Fin n)))]
      (fun x => hessianMatrix u x j i) := by
    filter_upwards [hGradLip.ae_differentiableAt (μ := volume)] with x hx
    exact hessian_coord_of_gradient_diff (i := j) (j := i) hx
  refine ⟨(hasWeakDerivAlong_of_lipschitz_readable hCoordLip (e j)).congr_ae_readable
    (Filter.Eventually.of_forall fun _ => rfl) hAE, ?_⟩
  intro S hS
  exact memLp_hessianMatrix_entry_of_isCompact hGradLip j i hS
/-- Compact-local essential boundedness of the total Hessian entry, reusing its
canonical measurability and Lipschitz-gradient pointwise bound. -/
private theorem FunctionalInequalities.Analysis.memLp_top_hessianMatrix_entry_of_isCompact {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {G : NNReal}
    (hGradLip : LipschitzWith G (gradient u)) (i j : Fin n)
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : IsCompact S) :
    MemLp (fun x => hessianMatrix u x i j) (⊤ : ENNReal)
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  let : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
    isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
  exact MemLp.of_bound
    (measurable_hessianMatrix_entry u i j).aestronglyMeasurable (G : ℝ)
    (Filter.Eventually.of_forall fun x => norm_hessianMatrix_entry_le_of_lipschitz_gradient_readable hGradLip x i j)
/-- Closed finite linearity for one negative term and a finite sum, encoded by
Option with coefficient -1 at none and 1 at every some. Kept local. -/
private theorem FunctionalInequalities.Analysis.hasWeakDerivAlong_neg_add_sum {n m : ℕ}
    {f₀ df₀ : EuclideanSpace ℝ (Fin n) → ℝ}
    {f df : Fin m → EuclideanSpace ℝ (Fin n) → ℝ}
    {v : EuclideanSpace ℝ (Fin n)}
    (h₀ : HasWeakDerivAlong f₀ df₀ v)
    (h₀₂ : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp df₀ 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hf : ∀ i : Fin m, HasWeakDerivAlong (f i) (df i) v)
    (hdf₂ : ∀ i : Fin m, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (df i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    HasWeakDerivAlong (fun x => -f₀ x + ∑ i : Fin m, f i x)
      (fun x => -df₀ x + ∑ i : Fin m, df i x) v ∧
    ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => -df₀ x + ∑ i : Fin m, df i x) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  let F : Option (Fin m) → EuclideanSpace ℝ (Fin n) → ℝ := fun i =>
    match i with
    | none => f₀
    | some i => f i
  let D : Option (Fin m) → EuclideanSpace ℝ (Fin n) → ℝ := fun i =>
    match i with
    | none => df₀
    | some i => df i
  let c : Option (Fin m) → ℝ := fun i =>
    match i with
    | none => -1
    | some _ => 1
  have hF (i : Option (Fin m)) : HasWeakDerivAlong (F i) (D i) v := by
    cases i with
    | none => exact h₀
    | some i => exact hf i
  have hD (i : Option (Fin m)) (S : Set (EuclideanSpace ℝ (Fin n))) (hS : IsCompact S) :
      MemLp (D i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
    cases i with
    | none => exact h₀₂ S hS
    | some i => exact hdf₂ i S hS
  have h := hasWeakDerivAlong_finsetSum_mul_readable (Finset.univ : Finset (Option (Fin m))) c
    (f := F) (df := D) (fun i _ => hF i) (fun i _ => hD i)
  simpa only [Fintype.sum_option, F, D, c, one_mul, neg_one_mul] using h
set_option maxHeartbeats 800000 in
/-- Weak derivative of the right-hand side `-∂ᵢu + Σₐ Hᵢₐ ∂ₐW(∇u)` of the first weak Monge–Ampère identity
along every coordinate, with compact-local L2 density, for a C1 potential with Lipschitz gradient, a C2
`W` and a given compact-local L2 weak Hessian tensor `T`. -/
theorem solution {n : ℕ}
    {u W : EuclideanSpace ℝ (Fin n) → ℝ}
    {L G : NNReal}
    (hu : ContDiff ℝ 1 u) (hL : LipschitzWith L u)
    (hG : LipschitzWith G (gradient u)) (hW : ContDiff ℝ 2 W)
    (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ)
    (hT : ∀ k i j : Fin n,
      FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => FunctionalInequalities.Probability.Stein.hessianMatrix u x i j) (fun x => T x k i j)
        (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => T x k i j) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    ∀ i j : Fin n,
      FunctionalInequalities.Analysis.HasWeakDerivAlong
        (fun x => -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) +
          ∑ a : Fin n, FunctionalInequalities.Probability.Stein.hessianMatrix u x i a *
            fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a))
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
          2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  intro i j
  have hPartial :=
    FunctionalInequalities.Analysis.hasWeakDerivAlong_fderiv_of_lipschitz_gradient hG i j
  have hProducts :
      ∀ a : Fin n,
        FunctionalInequalities.Analysis.HasWeakDerivAlong
          (fun x => FunctionalInequalities.Probability.Stein.hessianMatrix u x i a *
            fderiv ℝ W (gradient u x)
              (EuclideanSpace.basisFun (Fin n) ℝ a))
          (fun x =>
            T x j i a * fderiv ℝ W (gradient u x)
              (EuclideanSpace.basisFun (Fin n) ℝ a) +
            FunctionalInequalities.Probability.Stein.hessianMatrix u x i a *
              ∑ b : Fin n, FunctionalInequalities.Probability.Stein.hessianMatrix u x j b *
                FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x) b a)
          (EuclideanSpace.basisFun (Fin n) ℝ j) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp
            (fun x =>
              T x j i a * fderiv ℝ W (gradient u x)
                (EuclideanSpace.basisFun (Fin n) ℝ a) +
              FunctionalInequalities.Probability.Stein.hessianMatrix u x i a *
                ∑ b : Fin n, FunctionalInequalities.Probability.Stein.hessianMatrix u x j b *
                  FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x) b a)
            2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
    intro a
    obtain ⟨_, hCompLip, hComp⟩ :=
      FunctionalInequalities.Analysis.exists_lipschitzWith_weak_fderiv_comp_gradient_readable hu hL hG hW a
    exact
      (hT j i a).1.mul_of_locally_bounded_readable
        (hComp j).1
        (fun S hS =>
          FunctionalInequalities.Analysis.memLp_top_hessianMatrix_entry_of_isCompact hG i a S hS)
        (fun S hS =>
          FunctionalInequalities.Analysis.memLp_top_restrict_of_continuous hCompLip.continuous S hS)
        (hT j i a).2
        (hComp j).2
  exact
    FunctionalInequalities.Analysis.hasWeakDerivAlong_neg_add_sum
      hPartial.1 hPartial.2
      (fun a => (hProducts a).1)
      (fun a => (hProducts a).2)
