-- Prove2me | solution 1 for DriftLinBandit.BOB.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T16:55:27.358508+00:00
-- url     : https://prove2.me/submissions/c25340a2-6134-4cae-a071-3cec942ac0b8

import Mathlib
import Definitions.Def_DriftLinBandit_BOB_Model

open Matrix DriftLinBandit.BOB

namespace BOBLemma5Aux

lemma dot_mulVec_symm {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (hM : Mᵀ = M) (u v : Fin d → ℝ) :
    u ⬝ᵥ (M *ᵥ v) = v ⬝ᵥ (M *ᵥ u) := by
  rw [dotProduct_mulVec, ← hM, vecMul_transpose, hM, dotProduct_comm]

/-- Loewner antitonicity of the inverse, tested on one vector. -/
lemma quad_inv_le {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℝ) (hA : Aᵀ = A) (hB : Bᵀ = B)
    (hAu : IsUnit A) (hBu : IsUnit B) (hBpsd : ∀ y, 0 ≤ y ⬝ᵥ (B *ᵥ y))
    (hBA : ∀ y, y ⬝ᵥ (B *ᵥ y) ≤ y ⬝ᵥ (A *ᵥ y)) (x : Fin d → ℝ) :
    x ⬝ᵥ (A⁻¹ *ᵥ x) ≤ x ⬝ᵥ (B⁻¹ *ᵥ x) := by
  set u := A⁻¹ *ᵥ x with hu
  set v := B⁻¹ *ᵥ x with hv
  have hAu' : A *ᵥ u = x := by
    rw [hu, mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det A).1 hAu), one_mulVec]
  have hBv' : B *ᵥ v = x := by
    rw [hv, mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det B).1 hBu), one_mulVec]
  have h0 := hBpsd (u - v)
  have hexp : (u - v) ⬝ᵥ (B *ᵥ (u - v)) =
      u ⬝ᵥ (B *ᵥ u) - 2 * (u ⬝ᵥ (B *ᵥ v)) + v ⬝ᵥ (B *ᵥ v) := by
    rw [mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct,
      dot_mulVec_symm B hB v u]
    ring
  rw [hexp, hBv'] at h0
  have h1 := hBA u
  rw [hAu'] at h1
  rw [dotProduct_comm x u, dotProduct_comm x v]
  linarith

lemma gram_transpose {d : ℕ} (lam : ℝ) (X : ℕ → Fin d → ℝ) (W : Finset ℕ) :
    (gram lam X W)ᵀ = gram lam X W := by
  unfold DriftLinBandit.BOB.gram
  rw [transpose_add, transpose_smul, transpose_one, transpose_sum]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  ext i j; simp [vecMulVec_apply, mul_comm]

lemma gram_quad {d : ℕ} (lam : ℝ) (X : ℕ → Fin d → ℝ) (W : Finset ℕ) (y : Fin d → ℝ) :
    y ⬝ᵥ (gram lam X W *ᵥ y) = lam * (y ⬝ᵥ y) + ∑ s ∈ W, (X s ⬝ᵥ y) ^ 2 := by
  unfold DriftLinBandit.BOB.gram
  rw [add_mulVec, dotProduct_add, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]
  congr 1
  rw [sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [vecMulVec_mulVec, dotProduct_smul]
  simp [dotProduct_comm y (X s), sq]

lemma gram_isUnit {d : ℕ} (lam : ℝ) (hlam : 0 < lam) (X : ℕ → Fin d → ℝ) (W : Finset ℕ) :
    IsUnit (gram lam X W) := by
  rw [← mulVec_injective_iff_isUnit]
  intro a b hab
  have h : gram lam X W *ᵥ (a - b) = 0 := by rw [mulVec_sub, hab, sub_self]
  have hq := gram_quad lam X W (a - b)
  rw [h, dotProduct_zero] at hq
  have hs : 0 ≤ ∑ s ∈ W, (X s ⬝ᵥ (a - b)) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hdd : 0 ≤ (a - b) ⬝ᵥ (a - b) := by
    rw [dotProduct]; exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  have hz : (a - b) ⬝ᵥ (a - b) = 0 := by nlinarith
  exact sub_eq_zero.1 (dotProduct_self_eq_zero.1 hz)

lemma gram_mono_inv {d : ℕ} (lam : ℝ) (hlam : 0 < lam) (X : ℕ → Fin d → ℝ) (W W' : Finset ℕ)
    (hW : W ⊆ W') (x : Fin d → ℝ) :
    x ⬝ᵥ ((gram lam X W')⁻¹ *ᵥ x) ≤ x ⬝ᵥ ((gram lam X W)⁻¹ *ᵥ x) := by
  apply quad_inv_le _ _ (gram_transpose _ _ _) (gram_transpose _ _ _) (gram_isUnit _ hlam _ _)
    (gram_isUnit _ hlam _ _)
  · intro y
    rw [gram_quad]
    have hs : 0 ≤ ∑ s ∈ W, (X s ⬝ᵥ y) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hdd : 0 ≤ y ⬝ᵥ y := by
      rw [dotProduct]; exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _
    positivity
  · intro y
    rw [gram_quad, gram_quad]
    have := Finset.sum_le_sum_of_subset_of_nonneg hW
      (f := fun s => (X s ⬝ᵥ y) ^ 2) (fun _ _ _ => sq_nonneg _)
    linarith

end BOBLemma5Aux

open BOBLemma5Aux in
theorem solution {d : ℕ} (X : ℕ → Fin d → ℝ) (lam : ℝ) (hlam : 0 < lam) (w : ℕ) (hw : 1 ≤ w)
    (T : ℕ) (i : ℕ) (hi : i + 1 ≤ ⌈(T : ℝ) / (w : ℝ)⌉₊) :
    ∑ t ∈ Finset.Icc (i * w + 1) ((i + 1) * w),
        min 1 (X t ⬝ᵥ ((gram lam X (win 1 w t))⁻¹ *ᵥ X t)) ≤
      ∑ t ∈ Finset.Icc (i * w + 1) ((i + 1) * w),
        min 1 (X t ⬝ᵥ ((gram lam X (Finset.Icc (i * w + 1) (t - 1)))⁻¹ *ᵥ X t)) := by
  apply Finset.sum_le_sum
  intro t ht
  rw [Finset.mem_Icc] at ht
  apply min_le_min_left
  apply gram_mono_inv lam hlam X
  intro s hs
  rw [Finset.mem_Icc] at hs
  unfold win
  rw [Finset.mem_Icc]
  refine ⟨?_, hs.2⟩
  have : (i + 1) * w = i * w + w := by ring
  omega
