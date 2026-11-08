-- Prove2me | solution 1 for FermionModewise.eq_17
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:15:23.433452+00:00
-- url     : https://prove2.me/submissions/55eaeb65-f008-4bad-942c-cc1f306f9be1

import Mathlib

open Matrix

theorem solution {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (WA : Matrix m m ℝ) (WB : Matrix n n ℝ) (K : Matrix m n ℝ) (lam0 : ℝ)
    (h : Matrix.fromBlocks WA K (-Kᵀ) WB * Matrix.fromBlocks WA K (-Kᵀ) WB =
      (-(lam0 ^ 2)) • (1 : Matrix (m ⊕ n) (m ⊕ n) ℝ)) :
    WA * K + K * WB = 0 := by
  rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul] at h
  have h2 := congrArg Matrix.toBlocks₁₂ h
  simp only [Matrix.toBlocks_fromBlocks₁₂, smul_zero] at h2
  exact h2
