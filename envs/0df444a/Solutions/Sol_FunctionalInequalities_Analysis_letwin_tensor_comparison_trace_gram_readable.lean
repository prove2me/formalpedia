-- Prove2me | solution 1 for FunctionalInequalities.Analysis.letwin_tensor_comparison_trace_gram_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:41:48.886608+00:00
-- url     : https://prove2.me/submissions/7b1d4ebd-1cf9-4929-82ff-1839b4135b00

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_TraceGram
import Theorems.Thm_FunctionalInequalities_Analysis_letwin_tensor_comparison_readable
import Theorems.Thm_FunctionalInequalities_Analysis_trace_mul_mul_mul_eq_sum_readable

noncomputable section
open Matrix
private theorem FunctionalInequalities.Analysis.tensor_trace_gram_eq_four_sum {n : ℕ}
    (R : Matrix (Fin n) (Fin n) ℝ) (hR : R.IsHermitian)
    (T : Fin n → Fin n → Fin n → ℝ)
    (hT1 : ∀ a b c, T a b c = T b a c) (hT2 : ∀ a b c, T a b c = T a c b)
    (i j : Fin n) :
    (R * (Matrix.of fun a b => T i a b) * R * (Matrix.of fun a b => T j a b)).trace =
      ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
        R a c * R b d * T a b i * T c d j := by
  classical
  have hRs (a c : Fin n) : R c a = R a c := by
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M a c) hR.eq
    simpa only [Matrix.conjTranspose_apply, star_trivial] using h
  rw [trace_mul_mul_mul_eq_sum_readable]
  simp only [Fintype.sum_prod_type, Matrix.of_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  rw [hRs a c, hT1 i a b, hT2 a i b, hT2 j d c, hT1 j c d, hT2 c j d]
  ring
/-- Letwin's tensor comparison (arXiv:2607.24164v1 (2.12)) written in trace-Gram coordinates: for positive definite
`H`, symmetric `B` and a fully symmetric tensor `T`, `∑ H⁻¹ᵢⱼ tr(B Tᵢ B Tⱼ) ≤ tr(B H B G)` with
`G = (tr(H⁻¹ Tᵢ H⁻¹ Tⱼ))ᵢⱼ`. -/
theorem solution {n : ℕ}
    (H B : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosDef) (hB : B.IsHermitian)
    (T : Fin n → Fin n → Fin n → ℝ)
    (hT1 : ∀ a b c, T a b c = T b a c) (hT2 : ∀ a b c, T a b c = T a c b) :
    (∑ i : Fin n, ∑ j : Fin n, H⁻¹ i j *
      (B * (Matrix.of fun a b => T i a b) * B * (Matrix.of fun a b => T j a b)).trace) ≤
      (B * H * B * (Matrix.of fun i j =>
        (H⁻¹ * (Matrix.of fun a b => T i a b) * H⁻¹ *
          (Matrix.of fun a b => T j a b)).trace)).trace := by
  have h := FunctionalInequalities.Analysis.letwin_tensor_comparison_readable H B hH hB T hT1 hT2
  have he :
      (B * H * B * (Matrix.of fun i j =>
        (H⁻¹ * (Matrix.of fun a b => T i a b) * H⁻¹ *
          (Matrix.of fun a b => T j a b)).trace)).trace =
      ∑ i : Fin n, ∑ j : Fin n, (B * H * B) i j *
        ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
          H⁻¹ a c * H⁻¹ b d * T a b i * T c d j := by
    change (∑ i : Fin n, ∑ j : Fin n, (B * H * B) i j *
      (H⁻¹ * (Matrix.of fun a b => T j a b) * H⁻¹ *
        (Matrix.of fun a b => T i a b)).trace) = _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hs :
        (H⁻¹ * (Matrix.of fun a b => T j a b) * H⁻¹ *
          (Matrix.of fun a b => T i a b)).trace =
        (H⁻¹ * (Matrix.of fun a b => T i a b) * H⁻¹ *
          (Matrix.of fun a b => T j a b)).trace := by
      simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm
        (H⁻¹ * (Matrix.of fun a b => T j a b))
        (H⁻¹ * (Matrix.of fun a b => T i a b))
    rw [hs, FunctionalInequalities.Analysis.tensor_trace_gram_eq_four_sum H⁻¹ hH.inv.isHermitian T hT1 hT2 i j]
  rw [he]
  exact h
