-- Prove2me | solution 1 for FunctionalInequalities.Analysis.trace_forcing_add_twice_energy_nonneg_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:48:53.001732+00:00
-- url     : https://prove2.me/submissions/ad4a7e21-e5fd-4e22-ac05-a1875730d59b

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Theorems.Thm_FunctionalInequalities_Analysis_traceGram_posSemidef_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_trace_mul_nonneg_408915f

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
end TraceGram
end
end
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section TraceForcingDensity
open Matrix
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- For positive semidefinite `B`, `H`, `R`, `W` and symmetric `Tᵢ`, the pointwise trace density
`2 tr(B H B (-H + H W H + G_R)) + 2 ∑ R_{ij} tr(B Tᵢ B Tⱼ) + 2 tr(B H B H)` is nonnegative,
where `G_R` is the trace Gram matrix `tr(R Tᵢ R Tⱼ)`. -/
theorem solution {n : ℕ}
    (B H R W : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.PosSemidef) (hH : H.PosSemidef) (hR : R.PosSemidef) (hW : W.PosSemidef)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i : Fin n, (T i).IsSymm) :
    0 ≤ (2 * (B * H * B * (-H + H * W * H +
        (Matrix.of fun i j => (R * T i * R * T j).trace))).trace +
      2 * ∑ i : Fin n, ∑ j : Fin n, R i j * (B * T i * B * T j).trace) +
      2 * (B * H * B * H).trace := by
  classical
  have hC : (B * H * B).PosSemidef := by
    simpa only [hB.isHermitian.eq] using hH.mul_mul_conjTranspose_same B
  have hM : (H * W * H).PosSemidef := by
    simpa only [hH.isHermitian.eq] using hW.mul_mul_conjTranspose_same H
  have hG := FunctionalInequalities.Analysis.traceGram_posSemidef_408915f R hR T hT
  have h1 := FunctionalInequalities.Analysis.trace_mul_nonneg_408915f hC hM
  have h2 := FunctionalInequalities.Analysis.trace_mul_nonneg_408915f hC hG
  have h3 := FunctionalInequalities.Analysis.sum_entry_mul_nonneg hR (FunctionalInequalities.Analysis.traceGram_posSemidef_408915f B hB T hT)
  have he :
      (B * H * B * (-H + H * W * H +
        (Matrix.of fun i j => (R * T i * R * T j).trace))).trace =
      -(B * H * B * H).trace + (B * H * B * (H * W * H)).trace +
        (B * H * B * (Matrix.of fun i j => (R * T i * R * T j).trace)).trace := by
    simp only [mul_add, mul_neg, Matrix.trace_add, Matrix.trace_neg]
  rw [he]
  change 0 ≤ ∑ i : Fin n, ∑ j : Fin n, R i j * (B * T i * B * T j).trace at h3
  linarith
