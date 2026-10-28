-- Prove2me | solution 1 for FunctionalInequalities.Analysis.four_tensor_trace_le_density_add_twice_energy_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:42:48.600883+00:00
-- url     : https://prove2.me/submissions/ea0853bb-8e5b-449e-bcc4-3200be81f376

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Positivity
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_TraceGram
import Theorems.Thm_FunctionalInequalities_Analysis_letwin_tensor_comparison_trace_gram_readable
import Theorems.Thm_FunctionalInequalities_Analysis_traceGram_posSemidef_readable
import Theorems.Thm_FunctionalInequalities_Analysis_trace_mul_nonneg_readable

section
noncomputable section
open scoped MatrixOrder Kronecker
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

noncomputable section
open Matrix
/-- For positive semidefinite `B`, `W`, positive definite `H` and a fully symmetric tensor `T`, the trace tensor energy
`D = ∑ H⁻¹ᵢⱼ tr(B Tᵢ B Tⱼ)` satisfies `0 ≤ D` and `4 D ≤ g + 2 tr(B H B H)`, where `g` is the weak trace density
`2 tr(B H B (-H + H W H + G)) + 2 D`. -/
theorem solution {n : ℕ}
    (B H W : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.PosSemidef) (hH : H.PosDef) (hW : W.PosSemidef)
    (T : Fin n → Fin n → Fin n → ℝ)
    (hT1 : ∀ a b c, T a b c = T b a c) (hT2 : ∀ a b c, T a b c = T a c b) :
    let Tm := fun i => Matrix.of fun a b => T i a b
    let G := Matrix.of fun i j => (H⁻¹ * Tm i * H⁻¹ * Tm j).trace
    let D := ∑ i : Fin n, ∑ j : Fin n, H⁻¹ i j * (B * Tm i * B * Tm j).trace
    0 ≤ D ∧ 4 * D ≤
      (2 * (B * H * B * (-H + H * W * H + G)).trace + 2 * D) +
        2 * (B * H * B * H).trace := by
  classical
  dsimp only
  have hTm : ∀ i : Fin n, (Matrix.of fun a b => T i a b).IsSymm := by
    intro i
    ext a b
    exact hT2 i b a
  have hD := FunctionalInequalities.Analysis.sum_entry_mul_nonneg hH.inv.posSemidef (FunctionalInequalities.Analysis.traceGram_posSemidef_readable B hB
    (fun i => Matrix.of fun a b => T i a b) hTm)
  change 0 ≤ ∑ i : Fin n, ∑ j : Fin n, H⁻¹ i j *
    (B * (Matrix.of fun a b => T i a b) * B * (Matrix.of fun a b => T j a b)).trace at hD
  refine ⟨hD, ?_⟩
  have hC : (B * H * B).PosSemidef := by
    simpa only [hB.isHermitian.eq] using hH.posSemidef.mul_mul_conjTranspose_same B
  have hM : (H * W * H).PosSemidef := by
    simpa only [hH.isHermitian.eq] using hW.mul_mul_conjTranspose_same H
  have hA := FunctionalInequalities.Analysis.trace_mul_nonneg_readable hC hM
  have hCompare := FunctionalInequalities.Analysis.letwin_tensor_comparison_trace_gram_readable H B hH hB.isHermitian T hT1 hT2
  have he :
      (B * H * B * (-H + H * W * H + (Matrix.of fun i j =>
        (H⁻¹ * (Matrix.of fun a b => T i a b) * H⁻¹ *
          (Matrix.of fun a b => T j a b)).trace))).trace =
      -(B * H * B * H).trace + (B * H * B * (H * W * H)).trace +
        (B * H * B * (Matrix.of fun i j =>
          (H⁻¹ * (Matrix.of fun a b => T i a b) * H⁻¹ *
            (Matrix.of fun a b => T j a b)).trace)).trace := by
    simp only [mul_add, mul_neg, Matrix.trace_add, Matrix.trace_neg]
  rw [he]
  linarith
