-- Prove2me | solution 1 for DetANN.parseval_signed_blocks
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-14T01:01:45.911022+00:00
-- url     : https://prove2.me/submissions/06052a71-296d-43b4-806a-c66bb2bd01be

import Mathlib
import Definitions.Def_DetANN_SignedBlocks

open DetANN

namespace DetANNParsevalAux

lemma signOf_sq (b : Bool) : signOf b ^ 2 = 1 := by cases b <;> simp [signOf]

lemma blocks_normSq {d L : ℕ} (h : Matrix (Fin d) (Fin d) ℝ) (ξ : Fin L → Fin d → Bool)
    (j : Fin d) (z : EuclideanSpace ℝ (Fin d)) :
    ‖signedBlocks h L ξ j z‖ ^ 2 =
      ∑ ℓ : Fin L, ((Real.sqrt ((L : ℝ) * d))⁻¹ * ∑ r : Fin d, h j r * signOf (ξ ℓ r) * z r) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  simp only [signedBlocks, Real.norm_eq_abs, sq_abs]
  congr 1
  simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

/-- `∑_j (∑_r h_{jr} w_r)² = d ∑_r w_r²` when `hᵀh = d·I`. -/
lemma sum_sq_of_orth {d : ℕ} (h : Matrix (Fin d) (Fin d) ℝ)
    (hh : h.transpose * h = (d : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ)) (w : Fin d → ℝ) :
    ∑ j, (∑ r, h j r * w r) ^ 2 = d * ∑ r, w r ^ 2 := by
  have key : ∀ r r', ∑ j, h j r * h j r' = if r = r' then (d : ℝ) else 0 := by
    intro r r'
    have := congrFun (congrFun hh r) r'
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul, mul_ite, mul_one, mul_zero] at this
    exact this
  calc ∑ j, (∑ r, h j r * w r) ^ 2
      = ∑ j, ∑ r, ∑ r', (h j r * h j r') * (w r * w r') := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [sq, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun r' _ => ?_
        ring
    _ = ∑ r, ∑ r', (∑ j, h j r * h j r') * (w r * w r') := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun r' _ => ?_
        rw [Finset.sum_mul]
    _ = d * ∑ r, w r ^ 2 := by
        simp_rw [key, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        ring

end DetANNParsevalAux

open DetANNParsevalAux in
theorem solution {d : ℕ} (h : Matrix (Fin d) (Fin d) ℝ)
    (hh : h.transpose * h = (d : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ)) (L : ℕ) (hL : 1 ≤ L)
    (ξ : Fin L → Fin d → Bool) (z : EuclideanSpace ℝ (Fin d)) :
    ∑ j, ‖signedBlocks h L ξ j z‖ ^ 2 =
        (1 / (L : ℝ)) * ∑ ℓ : Fin L, ∑ j : Fin d,
          ((Real.sqrt d)⁻¹ * ∑ r : Fin d, h j r * signOf (ξ ℓ r) * z r) ^ 2 ∧
      ∑ j, ‖signedBlocks h L ξ j z‖ ^ 2 = ‖z‖ ^ 2 := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have first : ∑ j, ‖signedBlocks h L ξ j z‖ ^ 2 =
      (1 / (L : ℝ)) * ∑ ℓ : Fin L, ∑ j : Fin d,
        ((Real.sqrt d)⁻¹ * ∑ r : Fin d, h j r * signOf (ξ ℓ r) * z r) ^ 2 := by
    simp_rw [blocks_normSq]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Real.sqrt_mul hLpos.le, mul_inv, mul_pow, mul_pow, mul_pow, inv_pow, inv_pow,
      Real.sq_sqrt hLpos.le]
    ring
  refine ⟨first, ?_⟩
  rw [first]
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd; simp [EuclideanSpace.norm_eq]
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have inner : ∀ ℓ : Fin L, ∑ j : Fin d,
      ((Real.sqrt d)⁻¹ * ∑ r : Fin d, h j r * signOf (ξ ℓ r) * z r) ^ 2 = ‖z‖ ^ 2 := by
    intro ℓ
    have := sum_sq_of_orth h hh (fun r => signOf (ξ ℓ r) * z r)
    simp_rw [mul_pow, ← Finset.mul_sum]
    simp_rw [← mul_assoc] at this
    rw [this, inv_pow, Real.sq_sqrt hdpos.le, EuclideanSpace.norm_eq,
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    field_simp
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [signOf_sq, Real.norm_eq_abs, sq_abs, one_mul]
  simp_rw [inner]
  simp
  field_simp
