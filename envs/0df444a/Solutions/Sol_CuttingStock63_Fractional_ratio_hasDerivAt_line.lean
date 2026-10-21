-- Prove2me | solution 1 for CuttingStock63.Fractional.ratio_hasDerivAt_line
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:19:54.988335+00:00
-- url     : https://prove2.me/submissions/956ba4a3-7266-4cad-beb7-945e707d46e8

import Mathlib
import Definitions.Def_DermanSeqDecisions_LinProg_LinearFractional
set_option autoImplicit false
open DermanSeqDecisions.LinProg

theorem lin_line {n : ℕ} (c x v : Fin n → ℝ) (τ : ℝ) :
    ∑ i, c i * (x + τ • v) i = (∑ i, c i * x i) + τ * ∑ i, c i * v i := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem solution {n : ℕ} (c d x v : Fin n → ℝ) (hx : ∑ i, d i * x i ≠ 0) :
    HasDerivAt (fun τ : ℝ => fracObj c d (x + τ • v))
      (((∑ i, d i * x i) * (∑ i, c i * v i) - (∑ i, c i * x i) * (∑ i, d i * v i)) /
        (∑ i, d i * x i) ^ 2) 0 := by
  have hf : (fun τ : ℝ => fracObj c d (x + τ • v)) =
      fun τ : ℝ => ((∑ i, c i * x i) + τ * ∑ i, c i * v i) / ((∑ i, d i * x i) + τ * ∑ i, d i * v i) := by
    funext τ
    unfold fracObj
    rw [lin_line, lin_line]
  rw [hf]
  have h1 : HasDerivAt (fun τ : ℝ => (∑ i, c i * x i) + τ * ∑ i, c i * v i) (∑ i, c i * v i) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const (∑ i, c i * v i)).const_add (∑ i, c i * x i)
  have h2 : HasDerivAt (fun τ : ℝ => (∑ i, d i * x i) + τ * ∑ i, d i * v i) (∑ i, d i * v i) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const (∑ i, d i * v i)).const_add (∑ i, d i * x i)
  have h3 := h1.div h2 (by simpa using hx)
  refine h3.congr_deriv ?_
  simp only [zero_mul, add_zero]
  ring
