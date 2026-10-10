-- Prove2me | solution 1 for ConleyZehnder.complexLinearDet_mul_four_pow
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T17:09:24.038736+00:00
-- url     : https://prove2.me/submissions/10932611-f0f7-459c-9383-0eadb4d9265d

import Definitions.Def_ConleyZehnder_Setting

open ConleyZehnder Matrix

theorem solution {n : ℕ} (A : Mat n) :
    (4 : ℂ) ^ n * complexLinearDet A =
      ((A + 1).map (fun x : ℝ => (x : ℂ)) -
        Complex.I • (J₀ n * (A - 1)).map (fun x : ℝ => (x : ℂ))).det := by
  set M := ((A + 1).map (fun x : ℝ => (x : ℂ)) -
        Complex.I • (J₀ n * (A - 1)).map (fun x : ℝ => (x : ℂ))) with hMdef
  let a : Matrix (Fin n) (Fin n) ℂ := A.toBlocks₁₁.map (fun x : ℝ => (x : ℂ))
  let b : Matrix (Fin n) (Fin n) ℂ := A.toBlocks₁₂.map (fun x : ℝ => (x : ℂ))
  let c : Matrix (Fin n) (Fin n) ℂ := A.toBlocks₂₁.map (fun x : ℝ => (x : ℂ))
  let d : Matrix (Fin n) (Fin n) ℂ := A.toBlocks₂₂.map (fun x : ℝ => (x : ℂ))
  have hM : M = fromBlocks (a + 1 + Complex.I • c) (b - Complex.I • (1 - d))
      (c - Complex.I • (a - 1)) (d + 1 - Complex.I • b) := by
    ext (i | i) (j | j) <;>
      simp [M, a, b, c, d, J, mul_apply, Fintype.sum_sum_type, one_apply, toBlocks₁₁, toBlocks₁₂,
        toBlocks₂₁, toBlocks₂₂, fromBlocks] <;>
      split_ifs <;> push_cast <;> ring
  let L : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ := fromBlocks 1 0 (Complex.I • 1) 1
  let R : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ := fromBlocks 1 0 (-Complex.I • 1) 1
  have hL : L.det = 1 := by simp [L, det_fromBlocks_zero₁₂]
  have hR : R.det = 1 := by simp [R, det_fromBlocks_zero₁₂]
  have hI : ∀ X : Matrix (Fin n) (Fin n) ℂ, Complex.I • Complex.I • X = -X := fun X => by
    rw [smul_smul, Complex.I_mul_I, neg_smul, one_smul]
  have hLMR : L * M * R = fromBlocks ((a + d) + Complex.I • (c - b)) (b - Complex.I • (1 - d))
      0 ((2 : ℂ) • 1) := by
    rw [hM]
    simp only [L, R, fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul,
      Matrix.mul_zero, add_zero, zero_add, smul_mul_assoc, mul_smul_comm, Matrix.one_mul,
      Matrix.mul_one, smul_add, smul_sub, hI, neg_smul, smul_neg, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.sub_mul, Matrix.add_mul, neg_sub, neg_neg]
    congr 1
    · module
    · module
    · module
  have hdet : M.det = (2 : ℂ) ^ n * (2 : ℂ) ^ n * complexLinearDet A := by
    have := congrArg det hLMR
    rw [det_mul, det_mul, hL, hR, one_mul, mul_one, det_fromBlocks_zero₂₁, det_smul, det_one,
      Fintype.card_fin, mul_one] at this
    rw [this, complexLinearDet]
    have hX : (complexLinearPart A).toBlocks₁₁.map (fun x : ℝ => (x : ℂ)) +
        Complex.I • (complexLinearPart A).toBlocks₂₁.map (fun x : ℝ => (x : ℂ)) =
        (1 / 2 : ℂ) • ((a + d) + Complex.I • (c - b)) := by
      ext i j
      simp [complexLinearPart, a, b, c, d, J, mul_apply, Fintype.sum_sum_type, one_apply,
        toBlocks₁₁, toBlocks₁₂, toBlocks₂₁, toBlocks₂₂, fromBlocks]
      ring
    rw [hX, det_smul, Fintype.card_fin]
    have h2 : (2 : ℂ) ^ n * (1 / 2) ^ n = 1 := by rw [← mul_pow]; norm_num
    linear_combination (-(2 : ℂ) ^ n * (a + d + Complex.I • (c - b)).det) * h2
  rw [hdet, ← mul_pow]
  norm_num
