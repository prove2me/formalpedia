-- Prove2me | solution 1 for FunctionalInequalities.Analysis.symmetric_matrix_sqrt_real_cfc_bridge_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:41:21.495957+00:00
-- url     : https://prove2.me/submissions/de2f3587-f281-4a13-b79e-723553952863

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Sign

noncomputable section
open scoped MatrixOrder
section FiniteIndex
variable {ι : Type*}
variable [Fintype ι] [DecidableEq ι]
private lemma FunctionalInequalities.Analysis.matrix_sqrt_eq_real_cfc_of_nonneg
    (A : Matrix ι ι ℝ) (hA : 0 ≤ A) :
    CFC.sqrt A = cfc (fun x : ℝ => Real.sqrt x) A := by
  rw [CFC.sqrt_eq_cfc, cfc_nnreal_eq_real NNReal.sqrt A hA]
  apply cfc_congr
  intro x hx
  have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg hA hx
  calc
    (↑(NNReal.sqrt x.toNNReal) : ℝ) =
        Real.sqrt (x.toNNReal : ℝ) := by
          simp
    _ = Real.sqrt x := by
      rw [Real.coe_toNNReal x hx0]
/-- Positivity-derived bridge from the nonunital CFC square root to the real
unital CFC, specialized exactly to the two matrices used by the sign factorization.
No positivity hypothesis on `M` is added. -/
theorem solution
    (M : Matrix ι ι ℝ) (hM : M.IsSymm) :
    0 ≤ M * M ∧
      CFC.sqrt (M * M) = cfc (fun x : ℝ => Real.sqrt x) (M * M) ∧
      0 ≤ CFC.sqrt (M * M) ∧
      CFC.sqrt (CFC.sqrt (M * M)) =
        cfc (fun x : ℝ => Real.sqrt x) (CFC.sqrt (M * M)) := by
    have hct : M.conjTranspose = M := by
      exact (Matrix.conjTranspose_eq_transpose_of_trivial M).trans hM.eq
    have hMM : 0 ≤ M * M := by
      change (M * M - 0).PosSemidef
      simpa only [hct, sub_zero] using (Matrix.posSemidef_conjTranspose_mul_self M)
    have hsqrt : CFC.sqrt (M * M) =
        cfc (fun x : ℝ => Real.sqrt x) (M * M) :=
      FunctionalInequalities.Analysis.matrix_sqrt_eq_real_cfc_of_nonneg (M * M) hMM
    have hroot : 0 ≤ CFC.sqrt (M * M) :=
      CFC.sqrt_nonneg (M * M)
    have hsqrtroot :
        CFC.sqrt (CFC.sqrt (M * M)) =
          cfc (fun x : ℝ => Real.sqrt x) (CFC.sqrt (M * M)) :=
      FunctionalInequalities.Analysis.matrix_sqrt_eq_real_cfc_of_nonneg (CFC.sqrt (M * M)) hroot
    exact ⟨hMM, hsqrt, hroot, hsqrtroot⟩
