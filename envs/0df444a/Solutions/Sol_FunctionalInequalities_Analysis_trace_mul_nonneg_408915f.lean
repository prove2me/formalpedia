-- Prove2me | solution 1 for FunctionalInequalities.Analysis.trace_mul_nonneg_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:42:26.423231+00:00
-- url     : https://prove2.me/submissions/deebb1e8-7b3e-4270-bc39-9c307a8a84fc

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.LinearAlgebra.Matrix.Kronecker

noncomputable section
open scoped MatrixOrder Kronecker
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section TraceGram
open scoped BigOperators Kronecker
open Matrix
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
/-- Frobenius pairing of two real PSD matrices, proved using their Kronecker product.
No nonempty-index assumption is needed. -/
theorem FunctionalInequalities.Analysis.sum_entry_mul_nonneg {ι : Type*} [Fintype ι]
    {A C : Matrix ι ι ℝ} (hA : A.PosSemidef) (hC : C.PosSemidef) :
    0 ≤ ∑ i, ∑ j, A i j * C i j := by
  classical
  have h := (hA.kronecker hC).dotProduct_mulVec_nonneg
    (fun p : ι × ι => if p.1 = p.2 then (1 : ℝ) else 0)
  change 0 ≤ ∑ p : ι × ι,
    (if p.1 = p.2 then (1 : ℝ) else 0) *
      (∑ q : ι × ι, (A p.1 q.1 * C p.2 q.2) *
        (if q.1 = q.2 then (1 : ℝ) else 0)) at h
  simpa [Fintype.sum_prod_type, mul_ite, ite_mul] using h
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- The trace of a product of real PSD matrices is nonnegative; the product itself
is not asserted to be PSD. -/
theorem solution {ι : Type*} [Fintype ι]
    {A C : Matrix ι ι ℝ} (hA : A.PosSemidef) (hC : C.PosSemidef) :
    0 ≤ (A * C).trace := by
  classical
  have hs (i j : ι) : C j i = C i j := by
    have h := congrArg (fun M : Matrix ι ι ℝ => M i j) hC.isHermitian
    simpa only [Matrix.conjTranspose_apply, star_trivial] using h
  calc
    0 ≤ ∑ i, ∑ j, A i j * C i j := FunctionalInequalities.Analysis.sum_entry_mul_nonneg hA hC
    _ = (A * C).trace := by
      change (∑ i, ∑ j, A i j * C i j) =
        ∑ i, ∑ j, A i j * C j i
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hs i j]
