-- Prove2me | solution 1 for FunctionalInequalities.Analysis.fderiv_det_updateRow_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:29:34.27707+00:00
-- url     : https://prove2.me/submissions/76f93549-3b48-4590-ad75-23c09780b881

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_DeterminantDerivative
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Piola

section
noncomputable section
open scoped Matrix.Norms.Elementwise
section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- The determinant is differentiable (it is a continuous multilinear map of the rows). -/
theorem FunctionalInequalities.Analysis.differentiableAt_det (M : Matrix ι ι ℝ) : DifferentiableAt ℝ Matrix.det M :=
  (FunctionalInequalities.Analysis.detML.hasFDerivAt (fun i => M i)).differentiableAt
/-- The derivative of the determinant is the sum of row replacements. -/
theorem FunctionalInequalities.Analysis.fderiv_det_eq_sum_updateRow (M N : Matrix ι ι ℝ) :
    fderiv ℝ Matrix.det M N = ∑ i, (M.updateRow i (N i)).det := by
  change fderiv ℝ (FunctionalInequalities.Analysis.detML : (ι → ι → ℝ) → ℝ) (fun i => M i) (fun i => N i) = _
  rw [(FunctionalInequalities.Analysis.detML.hasFDerivAt (fun i => M i)).fderiv, ContinuousMultilinearMap.linearDeriv_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  rfl
end
end
end

noncomputable section
open Matrix
open FunctionalInequalities.Probability.Stein
 lemma solution
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E → Fin n → Fin n → ℝ) (x : E)
    (hA : ∀ k l, DifferentiableAt ℝ (fun y => A y k l) x)
    (j : Fin n) (c : Fin n → ℝ) (v : E) :
    fderiv ℝ (fun y => (Matrix.updateRow (A y) j c).det) x v =
      ∑ k, if k = j then 0
        else ((Matrix.updateRow (A x) j c).updateRow k
          (fun l => fderiv ℝ (fun y => A y k l) x v)).det := by
  let D : E →L[ℝ] Fin n → Fin n → ℝ :=
    ContinuousLinearMap.pi (fun k =>
      ContinuousLinearMap.pi (fun l =>
        if k = j then (0 : E →L[ℝ] ℝ)
        else fderiv ℝ (fun y => A y k l) x))
  let B : E → Fin n → Fin n → ℝ :=
    fun y k l => if k = j then c l else A y k l
  have hD : HasFDerivAt B D x := by
    apply hasFDerivAt_pi.mpr
    intro k
    apply hasFDerivAt_pi.mpr
    intro l
    by_cases h : k = j
    · simpa only [B, h, ite_true] using (hasFDerivAt_const (c l) x)
    · simpa only [B, h, ite_false] using (hA k l).hasFDerivAt
  have he :
      (fun y => (Matrix.updateRow (A y) j c).det) =
        (fun y => (Matrix.of (B y)).det) := by
    funext y
    congr 1
    ext k l
    exact Matrix.updateRow_apply
  rw [he]
  have hd :=
    congrArg (fun L : E →L[ℝ] ℝ => L v)
      ((FunctionalInequalities.Analysis.differentiableAt_det (Matrix.of (B x))).hasFDerivAt.comp x hD).fderiv
  change
    fderiv ℝ (fun y => (Matrix.of (B y)).det) x v =
      fderiv ℝ (fun M : Fin n → Fin n → ℝ => (Matrix.of M).det)
        (B x) (D v) at hd
  have hdet :=
    FunctionalInequalities.Analysis.fderiv_det_eq_sum_updateRow (Matrix.of (B x)) (Matrix.of (D v))
  change
    fderiv ℝ Matrix.det (Matrix.of (B x)) (Matrix.of (D v)) =
      ∑ k, ((Matrix.of (B x)).updateRow k (Matrix.of (D v) k)).det at hdet
  have hB : Matrix.of (B x) = Matrix.updateRow (Matrix.of (A x)) j c := by
    ext k l
    exact Matrix.updateRow_apply.symm
  calc
    fderiv ℝ (fun y => (Matrix.of (B y)).det) x v =
        fderiv ℝ (fun M : Fin n → Fin n → ℝ => (Matrix.of M).det)
          (B x) (D v) := hd
    _ = ∑ k, ((Matrix.of (B x)).updateRow k (Matrix.of (D v) k)).det := hdet
    _ = ∑ k, if k = j then 0
        else ((Matrix.updateRow (A x) j c).updateRow k
          (fun l => fderiv ℝ (fun y => A y k l) x v)).det := by
      rw [hB]
      apply Finset.sum_congr rfl
      intro k _
      by_cases h : k = j
      · subst k
        rw [if_pos rfl]
        apply Matrix.det_eq_zero_of_row_eq_zero j
        intro l
        rw [Matrix.updateRow_self]
        simp [D]
      · rw [if_neg h]
        have hr :
            (Matrix.of (D v)) k =
              fun l => fderiv ℝ (fun y => A y k l) x v := by
          funext l
          simp only [Matrix.of_apply, D, ContinuousLinearMap.pi_apply, if_neg h]
        rw [hr]
        rfl
