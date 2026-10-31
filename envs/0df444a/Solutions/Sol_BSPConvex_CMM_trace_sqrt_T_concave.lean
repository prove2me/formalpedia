-- Prove2me | solution 1 for BSPConvex.CMM.trace_sqrt_T_concave
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T14:48:57.424712+00:00
-- url     : https://prove2.me/submissions/51d5303c-5803-417c-bda6-37937edfef27

import Mathlib
import Definitions.Def_BSPConvex_CMM_Model
import Theorems.Thm_BSPConvex_CMM_lemma_6

open Matrix
open scoped MatrixOrder

open BSPConvex.CMM in
theorem BSPCMMAuxC.simplex_convex (m : ℕ) : Convex ℝ (simplex m) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun i => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    nlinarith [hx.2, hy.2, mul_le_mul_of_nonneg_left hx.2 ha, mul_le_mul_of_nonneg_left hy.2 hb]

open BSPConvex.CMM in
theorem solution {m : ℕ} (Sig : Matrix (Fin m) (Fin m) ℝ) (hSig : Sig.PosSemidef) :
    ConcaveOn ℝ (simplex m) (fCMM Sig) := by
  refine ⟨BSPCMMAuxC.simplex_convex m, ?_⟩
  intro x hx y hy a b ha hb hab
  obtain rfl : b = 1 - a := by linarith
  have hL := lemma_6 Sig hSig x y hx hy a ⟨ha, by linarith⟩
  have := hL.trace_nonneg
  rw [Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul,
    smul_eq_mul] at this
  simp only [fCMM, smul_eq_mul]
  linarith
