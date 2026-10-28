-- Prove2me | solution 1 for FunctionalInequalities.Analysis.ae_inverse_hessian_row_divergence_of_weak_derivative_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:40:12.850469+00:00
-- url     : https://prove2.me/submissions/3a219285-cd88-43ad-9922-bcd80364a569

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_Weak
import Theorems.Thm_FunctionalInequalities_Analysis_sum_integral_inv_hessianMatrix_mul_fderiv_eq_readable

noncomputable section
section WeakInverseRowDivergence
open MeasureTheory Set
open FunctionalInequalities.Probability.Stein
open scoped ContDiff RealInnerProductSpace Topology
/-- Weak Piola row divergence of the inverse Hessian at a fixed weak inverse-derivative object: for a C1
potential with Lipschitz gradient whose Hessian determinant is `exp F` a.e. with `F` Lipschitz, each row of
given inverse-Hessian weak derivatives sums to `-(H⁻¹ ∇F)` a.e., and `H⁻¹ ∇F` is L2 on compact sets. -/
theorem solution {n : ℕ}
    {u F : EuclideanSpace ℝ (Fin n) → ℝ}
    (hC1 : ContDiff ℝ 1 u) {G : NNReal} (hG : LipschitzWith G (gradient u))
    {LF : NNReal} (hF : LipschitzWith LF F)
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det = Real.exp (F x))
    (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ)
    (hInv : ∀ k i j : Fin n,
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
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    ∀ b : Fin n,
      (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp
          (fun x => ∑ a : Fin n, (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ b a *
            fderiv ℝ F x (EuclideanSpace.basisFun (Fin n) ℝ a))
          2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (∑ a : Fin n, -(((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ *
          (Matrix.of fun c d => T x a c d) * (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹) b a)) =
        -(∑ a : Fin n, (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ b a *
          fderiv ℝ F x (EuclideanSpace.basisFun (Fin n) ℝ a)) := by
  intro b
  let R : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ :=
    fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  let D : Fin n → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun a x => -((R x * (Matrix.of fun c d => T x a c d) * R x) b a)
  let z : Fin n → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun a x => R x b a * fderiv ℝ F x (e a)
  let g : EuclideanSpace ℝ (Fin n) → ℝ := fun x => ∑ a, z a x
  have hFLip : LipschitzWith LF F := hF
  have hDfMeas (a : Fin n) : Measurable (fun x => fderiv ℝ F x (e a)) :=
    (show Continuous (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => A (e a)) from
      continuous_id.clm_apply continuous_const).measurable.comp (measurable_fderiv ℝ F)
  have hDfBound (a : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
      ‖fderiv ℝ F x (e a)‖ ≤ (LF : ℝ) := by
    have hh := (fderiv ℝ F x).le_opNorm (e a)
    rw [e.norm_eq_one a, mul_one] at hh
    exact hh.trans (norm_fderiv_le_of_lipschitz ℝ hFLip)
  have hz2 (a : Fin n) (S : Set (EuclideanSpace ℝ (Fin n))) (hS : IsCompact S) :
      MemLp (z a) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
    let : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
      isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
    have hdf2 : MemLp (fun x => fderiv ℝ F x (e a)) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
      MemLp.of_bound (hDfMeas a).aestronglyMeasurable (LF : ℝ)
        (Filter.Eventually.of_forall (hDfBound a))
    exact hdf2.mul' ((hInv a b a).2.2 S hS)
  have hg2 (S : Set (EuclideanSpace ℝ (Fin n))) (hS : IsCompact S) :
      MemLp g 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
    exact memLp_finsetSum Finset.univ (fun a _ => hz2 a S hS)
  have hzLocal (a : Fin n) : LocallyIntegrable (z a)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply locallyIntegrable_iff.mpr
    intro S hS
    let : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
      isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
    exact (hz2 a S hS).integrable (by norm_num)
  have hgLocal : LocallyIntegrable g
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    locallyIntegrable_finsetSum Finset.univ (fun a _ => hzLocal a)
  have hDLocal (a : Fin n) : LocallyIntegrable (D a)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := (hInv a b a).1.2.1
  have hsumLocal : LocallyIntegrable (fun x => ∑ a, D a x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    locallyIntegrable_finsetSum Finset.univ (fun a _ => hDLocal a)
  refine ⟨hg2, ?_⟩
  apply ae_eq_of_integral_contDiff_smul_eq hsumLocal hgLocal.neg
  intro ψ hψ hψc
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨Lψ, hψLip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hψc hψ1 one_ne_zero
  have hPiola := FunctionalInequalities.Analysis.sum_integral_inv_hessianMatrix_mul_fderiv_eq_readable
    hC1 hG hFLip hdet hψLip hψc b
  have hDi (a : Fin n) : Integrable (fun x => D a x * ψ x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    simpa only [smul_eq_mul, mul_comm] using
      (hDLocal a).integrable_smul_left_of_hasCompactSupport hψ.continuous hψc
  have hzi (a : Fin n) : Integrable (fun x => z a x * ψ x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    simpa only [smul_eq_mul, mul_comm] using
      (hzLocal a).integrable_smul_left_of_hasCompactSupport hψ.continuous hψc
  have hweak : (∑ a, ∫ x, R x b a * fderiv ℝ ψ x (e a)) =
      -(∑ a, ∫ x, D a x * ψ x) := by
    calc
      _ = ∑ a, -(∫ x, D a x * ψ x) := by
        apply Finset.sum_congr rfl
        intro a _
        exact (hInv a b a).1.2.2 ψ hψ1 hψc
      _ = _ := by rw [Finset.sum_neg_distrib]
  have hID : (∫ x, (∑ a, D a x) * ψ x) = ∑ a, ∫ x, D a x * ψ x := by
    simp only [Finset.sum_mul]
    exact integral_finsetSum Finset.univ (fun a _ => hDi a)
  have hIz : (∫ x, g x * ψ x) = ∑ a, ∫ x, z a x * ψ x := by
    change (∫ x, (∑ a, z a x) * ψ x) = _
    simp only [Finset.sum_mul]
    exact integral_finsetSum Finset.univ (fun a _ => hzi a)
  have hEq : (∫ x, (∑ a, D a x) * ψ x) = -(∫ x, g x * ψ x) := by
    rw [hID, hIz]
    change (∑ a, ∫ x, R x b a * fderiv ℝ ψ x (e a)) =
      (∑ a, ∫ x, z a x * ψ x) at hPiola
    linarith only [hweak, hPiola]
  simpa only [smul_eq_mul, Pi.neg_apply, mul_neg, integral_neg, mul_comm] using hEq
