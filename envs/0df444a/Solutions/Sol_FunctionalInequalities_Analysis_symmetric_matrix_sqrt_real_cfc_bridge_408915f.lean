-- Prove2me | solution 1 for FunctionalInequalities.Analysis.symmetric_matrix_sqrt_real_cfc_bridge_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:48:42.784043+00:00
-- url     : https://prove2.me/submissions/f874ce3d-dd49-45c4-8d6b-17f2629f3b90

import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NoncommRing

noncomputable section
open scoped MatrixOrder
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
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
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
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
      matrix_sqrt_eq_real_cfc_of_nonneg (M * M) hMM
    have hroot : 0 ≤ CFC.sqrt (M * M) :=
      CFC.sqrt_nonneg (M * M)
    have hsqrtroot :
        CFC.sqrt (CFC.sqrt (M * M)) =
          cfc (fun x : ℝ => Real.sqrt x) (CFC.sqrt (M * M)) :=
      matrix_sqrt_eq_real_cfc_of_nonneg (CFC.sqrt (M * M)) hroot
    exact ⟨hMM, hsqrt, hroot, hsqrtroot⟩
