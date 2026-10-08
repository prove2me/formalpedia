-- Prove2me | solution 1 for BurerMonteiro.RankIncrease.eq9_lagrangian_second_derivative
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T04:02:44.536619+00:00
-- url     : https://prove2.me/submissions/7a005338-cf0f-4b9a-a445-af5b1cafe9b9

import Mathlib
import Definitions.Def_BurerMonteiro_RankIncrease_SDP
import Definitions.Def_BurerMonteiro_RankIncrease_Nr

open Matrix
open scoped Matrix.Norms.Frobenius

namespace C3cf4d76Aux

open BurerMonteiro.RankIncrease

lemma frob_add_right {p q : ℕ} (G X Y : Matrix (Fin p) (Fin q) ℝ) :
    frob G (X + Y) = frob G X + frob G Y := by
  simp [frob, Matrix.mul_add, Matrix.trace_add]

lemma frob_smul_right {p q : ℕ} (G X : Matrix (Fin p) (Fin q) ℝ) (c : ℝ) :
    frob G (c • X) = c * frob G X := by
  simp [frob, Matrix.mul_smul, Matrix.trace_smul]

lemma lagrangian_eq {n m r : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ) (X : Matrix (Fin n) (Fin r) ℝ)
    (y : Fin m → ℝ) :
    lagrangian C A b X y = frob (slack C A y) (X * Xᵀ) + ∑ i, y i * b i := by
  unfold lagrangian slack frob
  rw [Matrix.transpose_sub, Matrix.sub_mul, Matrix.trace_sub, Matrix.transpose_sum,
    Matrix.sum_mul, Matrix.trace_sum]
  simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, mul_sub,
    Finset.sum_sub_distrib]
  ring

lemma expand {n r : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (R D : Matrix (Fin n) (Fin r) ℝ) (s : ℝ) :
    frob S ((R + s • D) * (R + s • D)ᵀ) =
      frob S (R * Rᵀ) + s * frob S (R * Dᵀ + D * Rᵀ) + s ^ 2 * frob S (D * Dᵀ) := by
  have h : (R + s • D) * (R + s • D)ᵀ = R * Rᵀ + s • (R * Dᵀ + D * Rᵀ) + (s ^ 2) • (D * Dᵀ) := by
    rw [Matrix.transpose_add, Matrix.transpose_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, smul_add, pow_two]
    abel
  rw [h, frob_add_right, frob_add_right, frob_smul_right, frob_smul_right]

end C3cf4d76Aux

open BurerMonteiro.RankIncrease Matrix in
theorem solution {n m : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ) (hC : C.IsSymm)
    (hA : ∀ i, (A i).IsSymm) {r : ℕ} (hr0 : 0 < r) (hrn : r ≤ n)
    (R D : Matrix (Fin n) (Fin r) ℝ) (y : Fin m → ℝ) :
    HasDerivAt (fun t : ℝ => deriv (fun s : ℝ => lagrangian C A b (R + s • D) y) t)
      (2 * frob (slack C A y) (D * Dᵀ)) 0 := by
  set c0 := frob (slack C A y) (R * Rᵀ) + ∑ i, y i * b i
  set c1 := frob (slack C A y) (R * Dᵀ + D * Rᵀ)
  set c2 := frob (slack C A y) (D * Dᵀ)
  have hf : (fun s : ℝ => lagrangian C A b (R + s • D) y) = fun s => c0 + s * c1 + s ^ 2 * c2 := by
    funext s
    rw [C3cf4d76Aux.lagrangian_eq, C3cf4d76Aux.expand]
    ring
  have hd : (fun t : ℝ => deriv (fun s : ℝ => lagrangian C A b (R + s • D) y) t) =
      fun t => c1 + 2 * c2 * t := by
    funext t
    rw [hf]
    have : HasDerivAt (fun s : ℝ => c0 + s * c1 + s ^ 2 * c2) (c1 + 2 * c2 * t) t :=
      ((((hasDerivAt_id' t).mul_const c1).const_add c0).add
        ((hasDerivAt_pow 2 t).mul_const c2)).congr_deriv (by norm_num <;> ring)
    exact this.deriv
  rw [hd]
  exact (((hasDerivAt_id' (0:ℝ)).const_mul (2 * c2)).const_add c1).congr_deriv (by ring)
