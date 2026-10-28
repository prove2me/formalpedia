-- Prove2me | solution 1 for FunctionalInequalities.Analysis.exists_weak_hessian_adjugate_derivative_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:43:18.721862+00:00
-- url     : https://prove2.me/submissions/5f330573-c674-4174-b15d-6ae60d55ca85

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Piola
import Theorems.Thm_FunctionalInequalities_Analysis_hasWeakDerivAlong_det_of_locally_memLp_two_readable
import Theorems.Thm_FunctionalInequalities_Analysis_hasWeakDerivAlong_of_contDiff_readable

noncomputable section
open Matrix
open FunctionalInequalities.Probability.Stein
section WeakHessianAdjugateConsumers
open MeasureTheory Set Filter Metric Matrix
open scoped ContDiff Topology Matrix.Norms.Elementwise
/-- Existing cofactor proof core, for the same supplied actual tensor. -/
theorem solution {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ}
    (hbound : ∀ r s : Fin n, MemLp (fun x => FunctionalInequalities.Probability.Stein.hessianMatrix u x r s)
      (⊤ : ENNReal) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hT : ∀ k i j : Fin n,
      FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => FunctionalInequalities.Probability.Stein.hessianMatrix u x i j) (fun x => T x k i j)
        (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => T x k i j) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (k i j : Fin n) :
    ∃ g : EuclideanSpace ℝ (Fin n) → ℝ,
      FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x).adjugate i j) g
        (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp g 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  classical
  let A : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ :=
    fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x).updateRow j (Pi.single i 1)
  let DA : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ :=
    fun x => (Matrix.of fun r s => T x k r s).updateRow j (fun _ => 0)
  have hA (r s : Fin n) : FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => A x r s)
      (fun x => DA x r s) (EuclideanSpace.basisFun (Fin n) ℝ k) := by
    by_cases hr : r = j
    · subst r
      simpa [A, DA, Matrix.updateRow_apply] using
        (FunctionalInequalities.Analysis.hasWeakDerivAlong_of_contDiff_readable
          (f := fun _ : EuclideanSpace ℝ (Fin n) => (Pi.single i (1 : ℝ) : Fin n → ℝ) s)
          contDiff_const (EuclideanSpace.basisFun (Fin n) ℝ k))
    · simpa [A, DA, Matrix.updateRow_apply, hr] using (hT k r s).1
  have hAb (r s : Fin n) : MemLp (fun x => A x r s) (⊤ : ENNReal)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    by_cases hr : r = j
    · subst r
      simpa [A, Matrix.updateRow_apply] using
        (memLp_top_const ((Pi.single i (1 : ℝ) : Fin n → ℝ) s)
          (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))))
    · simpa [A, Matrix.updateRow_apply, hr] using hbound r s
  have hDA2 (r s : Fin n) (S : Set (EuclideanSpace ℝ (Fin n))) (hS : IsCompact S) :
      MemLp (fun x => DA x r s) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
    by_cases hr : r = j
    · subst r
      simp [DA, Matrix.updateRow_apply]
    · simpa [DA, Matrix.updateRow_apply, hr] using (hT k r s).2 S hS
  have hp := FunctionalInequalities.Analysis.hasWeakDerivAlong_det_of_locally_memLp_two_readable hA hAb hDA2
  refine ⟨_, ?_, hp.2⟩
  simpa only [Matrix.adjugate_apply] using hp.1
