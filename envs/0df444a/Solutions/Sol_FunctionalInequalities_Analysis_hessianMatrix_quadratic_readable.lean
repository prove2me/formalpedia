-- Prove2me | solution 1 for FunctionalInequalities.Analysis.hessianMatrix_quadratic_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:32:38.175974+00:00
-- url     : https://prove2.me/submissions/17ad2bfc-1bb5-4368-98ed-8f4468b7f2a0

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Viscosity

noncomputable section
open Set Metric Filter
open scoped RealInnerProductSpace Topology
open FunctionalInequalities.Probability.Stein
section LT12C2TaylorHessianBound
private lemma FunctionalInequalities.Analysis.matrix_quadratic_formula
    {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin n)) :
    ⟪v, Matrix.toEuclideanLin M v⟫ =
      ∑ i, ∑ j, v.ofLp i * (M i j * v.ofLp j) := by
  rw [Matrix.toLpLin_apply 2 2, PiLp.inner_apply]
  simp [Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring
 lemma solution
    {n : ℕ} {ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)}
    (v : EuclideanSpace ℝ (Fin n)) :
    ⟪v, Matrix.toEuclideanLin (FunctionalInequalities.Probability.Stein.hessianMatrix ψ x) v⟫ =
      (fderiv ℝ (fderiv ℝ ψ) x) v v := by
  classical
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let H : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    fderiv ℝ (fderiv ℝ ψ) x
  let c : Fin n → ℝ := fun i => (b.repr v).ofLp i
  have hv : ∑ i, c i • b i = v := b.sum_repr v
  have hc : ∀ i, c i = v.ofLp i := by
    intro i
    exact (EuclideanSpace.basisFun_repr (Fin n) ℝ v i).symm
  have hentry : ∀ i j, FunctionalInequalities.Probability.Stein.hessianMatrix ψ x i j = H (b i) (b j) := by
    intro i j
    change
      bilinearIteratedFDerivTwo ℝ ψ x (b i) (b j) =
        H (b i) (b j)
    rw [bilinearIteratedFDerivTwo_eq_iteratedFDeriv]
    simpa [H] using iteratedFDeriv_two_apply ψ x ![b i, b j]
  have hfirst :
      H (∑ i, c i • b i) = ∑ i, H (c i • b i) := by
    rw [map_sum]
  have hsecond :
      ∀ i, (H (c i • b i)) (∑ j, c j • b j) =
        ∑ j, (H (c i • b i)) (c j • b j) := by
    intro i
    rw [map_sum]
  have hsum :
      H (∑ i, c i • b i) (∑ j, c j • b j) =
        ∑ i, ∑ j, c i * (H (b i) (b j) * c j) := by
    calc
      H (∑ i, c i • b i) (∑ j, c j • b j) =
          (∑ i, H (c i • b i)) (∑ j, c j • b j) := by
            rw [hfirst]
      _ = ∑ i, (H (c i • b i)) (∑ j, c j • b j) := by
            rw [sum_apply]
      _ = ∑ i, ∑ j, c i * (H (b i) (b j) * c j) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hsecond i]
            simp only [map_smul, smul_apply, smul_eq_mul]
            apply Finset.sum_congr rfl
            intro j hj
            ring
  rw [FunctionalInequalities.Analysis.matrix_quadratic_formula]
  simp_rw [hentry, ← hc]
  rw [← hsum, hv]
