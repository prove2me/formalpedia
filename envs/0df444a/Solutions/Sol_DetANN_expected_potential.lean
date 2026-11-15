-- Prove2me | solution 1 for DetANN.expected_potential
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-14T10:04:19.470873+00:00
-- url     : https://prove2.me/submissions/c691627b-6127-45de-9bf6-63764b054aa3

import Mathlib
import Definitions.Def_DetANN_SignedBlocks
import Theorems.Thm_DetANN_lemma_6_1

open DetANN

namespace DetANNExpPotAux

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

/-- Identity (23): with `a_r = h_{jr} v_r`,
`d‖A_j v‖² − ‖v‖² = (1/L) ∑_ℓ ((∑_r a_r ξ_{ℓr})² − ∑_r a_r²)`. -/
lemma identity_23 {d L : ℕ} (hd : 1 ≤ d) (hL : 1 ≤ L) (h : Matrix (Fin d) (Fin d) ℝ)
    (hpm : ∀ j r, h j r = 1 ∨ h j r = -1) (ξ : Fin L → Fin d → Bool) (j : Fin d)
    (v : EuclideanSpace ℝ (Fin d)) :
    (d : ℝ) * ‖signedBlocks h L ξ j v‖ ^ 2 - ‖v‖ ^ 2 =
      (1 / (L : ℝ)) * ∑ ℓ : Fin L, ((∑ r, (h j r * v r) * signOf (ξ ℓ r)) ^ 2 -
        ∑ r, (h j r * v r) ^ 2) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hsq : ∀ r, (h j r * v r) ^ 2 = v r ^ 2 := by
    intro r; rcases hpm j r with e | e <;> rw [e] <;> ring
  have hv : ‖v‖ ^ 2 = ∑ r, (h j r * v r) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]; exact Finset.sum_congr rfl fun r _ => (hsq r).symm
  rw [blocks_normSq, hv, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hc : ((Real.sqrt ((L : ℝ) * d))⁻¹) ^ 2 = 1 / ((L : ℝ) * d) := by
    rw [inv_pow, Real.sq_sqrt (by positivity), one_div]
  have hterm : ∀ ℓ : Fin L, ((Real.sqrt ((L : ℝ) * d))⁻¹ *
      ∑ r : Fin d, h j r * signOf (ξ ℓ r) * v r) ^ 2 =
      1 / ((L : ℝ) * d) * (∑ r, (h j r * v r) * signOf (ξ ℓ r)) ^ 2 := by
    intro ℓ
    rw [mul_pow, hc]
    congr 2
    exact Finset.sum_congr rfl fun r _ => by ring
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  field_simp

end DetANNExpPotAux

open DetANNExpPotAux in
theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∃ C₀s : ℝ, 0 < C₀s ∧ ∀ C₀ : ℝ, C₀s ≤ C₀ → ∀ d : ℕ, 1 ≤ d →
      ∀ h : Matrix (Fin d) (Fin d) ℝ, (∀ j r, h j r = 1 ∨ h j r = -1) →
        ∀ τ : ℝ, 0 < τ → τ < 1 →
          ∀ D : Finset (EuclideanSpace ℝ (Fin d)), (∀ v ∈ D, v ≠ 0) → 1 ≤ D.card →
            (Fintype.card (Fin (numReps C₀ τ (momentOrder D.card d)) → Fin d → Bool) : ℝ)⁻¹ *
                ∑ ξ : Fin (numReps C₀ τ (momentOrder D.card d)) → Fin d → Bool,
                  potential h (numReps C₀ τ (momentOrder D.card d)) ξ τ (momentOrder D.card d) D
              ≤ (D.card : ℝ) * d * (C * momentOrder D.card d /
                  ((numReps C₀ τ (momentOrder D.card d) : ℝ) * τ ^ 2)) ^ momentOrder D.card d ∧
            (D.card : ℝ) * d * (C * momentOrder D.card d /
                  ((numReps C₀ τ (momentOrder D.card d) : ℝ) * τ ^ 2)) ^ momentOrder D.card d
              ≤ (D.card : ℝ) * d * (4 : ℝ)⁻¹ ^ momentOrder D.card d ∧
            (D.card : ℝ) * d * (4 : ℝ)⁻¹ ^ momentOrder D.card d ≤ 1 / 8 := by
  obtain ⟨C, hC, h61⟩ := lemma_6_1
  refine ⟨C, hC, max (4 * C) 1, by positivity, ?_⟩
  intro C₀ hC₀ d hd h hpm τ hτ0 hτ1 D hD hN
  set N := D.card with hNdef
  set p₀ := momentOrder N d with hp₀def
  set L := numReps C₀ τ p₀ with hLdef
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hC₀1 : 1 ≤ C₀ := le_trans (le_max_right _ _) hC₀
  have hC₀4 : 4 * C ≤ C₀ := le_trans (le_max_left _ _) hC₀
  -- 8Nd ≥ 8 > 4, so p₀ = ⌈log₄(8Nd)⌉ ≥ 1 and 4^{p₀} ≥ 8Nd
  have h8 : (8 : ℝ) ≤ 8 * N * d := by
    have : (1 : ℝ) ≤ N * d := one_le_mul_of_one_le_of_one_le hNR (by exact_mod_cast hd)
    nlinarith
  have hp₀pos : 1 ≤ p₀ := by
    rw [hp₀def, momentOrder, Nat.one_le_ceil_iff]
    exact Real.logb_pos (by norm_num) (by push_cast; linarith)
  have hp₀R : (1 : ℝ) ≤ p₀ := by exact_mod_cast hp₀pos
  have h4p : 8 * (N : ℝ) * d ≤ 4 ^ p₀ := by
    have hle : Real.logb 4 (8 * N * d) ≤ p₀ := by
      rw [hp₀def, momentOrder]; push_cast; exact Nat.le_ceil _
    rw [Real.logb_le_iff_le_rpow (by norm_num) (by positivity), Real.rpow_natCast] at hle
    exact hle
  -- L ≥ C₀ τ⁻² p₀ ≥ p₀ ≥ 1, and L τ² ≥ 4 C p₀
  have hτ2 : 0 < τ ^ 2 := by positivity
  have hτ2le : τ ^ 2 ≤ 1 := by nlinarith
  have hLge : C₀ * (τ ^ 2)⁻¹ * p₀ ≤ (L : ℝ) := by rw [hLdef, numReps]; exact Nat.le_ceil _
  have hLp : (p₀ : ℝ) ≤ L := by
    have : (p₀ : ℝ) ≤ C₀ * (τ ^ 2)⁻¹ * p₀ := by
      have : (1 : ℝ) ≤ C₀ * (τ ^ 2)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ hτ2]; nlinarith
      nlinarith
    linarith
  have hLpN : p₀ ≤ L := by exact_mod_cast hLp
  have hL1 : 1 ≤ L := le_trans hp₀pos hLpN
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL1
  have hLτ : 4 * C * p₀ ≤ L * τ ^ 2 := by
    have := mul_le_mul_of_nonneg_right hLge hτ2.le
    rw [show C₀ * (τ ^ 2)⁻¹ * p₀ * τ ^ 2 = C₀ * p₀ by field_simp] at this
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · -- (i) E Φ ≤ N d (C p₀/(L τ²))^{p₀}, from Lemma 6.1 and identity (23)
    set K : ℝ := (Fintype.card (Fin L → Fin d → Bool) : ℝ)⁻¹ with hK
    unfold potential
    have hswap : K * ∑ ξ : Fin L → Fin d → Bool, ∑ v ∈ D, ∑ j : Fin d,
        (((d : ℝ) * ‖signedBlocks h L ξ j v‖ ^ 2 - ‖v‖ ^ 2) / (τ * ‖v‖ ^ 2)) ^ (2 * p₀) =
        ∑ v ∈ D, ∑ j : Fin d, K * ∑ ξ : Fin L → Fin d → Bool,
          (((d : ℝ) * ‖signedBlocks h L ξ j v‖ ^ 2 - ‖v‖ ^ 2) / (τ * ‖v‖ ^ 2)) ^ (2 * p₀) := by
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [Finset.sum_comm, Finset.mul_sum]
    rw [hswap]
    have hbound : ∀ v ∈ D, ∀ j : Fin d, K * ∑ ξ : Fin L → Fin d → Bool,
        (((d : ℝ) * ‖signedBlocks h L ξ j v‖ ^ 2 - ‖v‖ ^ 2) / (τ * ‖v‖ ^ 2)) ^ (2 * p₀) ≤
        (C * p₀ / (L * τ ^ 2)) ^ p₀ := by
      intro v hvD j
      have hv0 : 0 < ‖v‖ ^ 2 := by have := norm_pos_iff.2 (hD v hvD); positivity
      set a : Fin d → ℝ := fun r => h j r * v r
      have ha : ∑ r, a r ^ 2 = ‖v‖ ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq]
        refine Finset.sum_congr rfl fun r _ => ?_
        simp only [a]; rcases hpm j r with e | e <;> rw [e] <;> ring
      have h61' := h61 (Fin d) a L p₀ hp₀pos hLpN
      have hrw : ∀ ξ : Fin L → Fin d → Bool,
          (((d : ℝ) * ‖signedBlocks h L ξ j v‖ ^ 2 - ‖v‖ ^ 2) / (τ * ‖v‖ ^ 2)) ^ (2 * p₀) =
          ((L : ℝ) * τ * ‖v‖ ^ 2)⁻¹ ^ (2 * p₀) *
            (∑ ℓ : Fin L, ((∑ r, a r * signOf (ξ ℓ r)) ^ 2 - ∑ r, a r ^ 2)) ^ (2 * p₀) := by
        intro ξ
        simp only [a]
        rw [identity_23 hd hL1 h hpm ξ j v, ← mul_pow]
        congr 1
        field_simp
      simp_rw [hrw]
      rw [← Finset.mul_sum, mul_left_comm]
      calc ((L : ℝ) * τ * ‖v‖ ^ 2)⁻¹ ^ (2 * p₀) * (K * ∑ ξ : Fin L → Fin d → Bool,
            (∑ ℓ : Fin L, ((∑ r, a r * signOf (ξ ℓ r)) ^ 2 - ∑ r, a r ^ 2)) ^ (2 * p₀))
          ≤ ((L : ℝ) * τ * ‖v‖ ^ 2)⁻¹ ^ (2 * p₀) *
              ((C * p₀ * L) ^ p₀ * (∑ r, a r ^ 2) ^ (2 * p₀)) := by
            gcongr
        _ = (C * p₀ / (L * τ ^ 2)) ^ p₀ := by
            have hvne : ‖v‖ ≠ 0 := (norm_pos_iff.2 (hD v hvD)).ne'
            rw [ha, pow_mul, pow_mul, inv_pow, ← mul_pow, ← mul_pow]
            congr 1
            field_simp
    calc ∑ v ∈ D, ∑ j : Fin d, K * ∑ ξ : Fin L → Fin d → Bool,
          (((d : ℝ) * ‖signedBlocks h L ξ j v‖ ^ 2 - ‖v‖ ^ 2) / (τ * ‖v‖ ^ 2)) ^ (2 * p₀)
        ≤ ∑ v ∈ D, ∑ j : Fin d, (C * p₀ / (L * τ ^ 2)) ^ p₀ :=
          Finset.sum_le_sum fun v hv => Finset.sum_le_sum fun j _ => hbound v hv j
      _ = (N : ℝ) * d * (C * p₀ / (L * τ ^ 2)) ^ p₀ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  · -- (ii) C p₀/(L τ²) ≤ 1/4
    have hq : C * p₀ / (L * τ ^ 2) ≤ (4 : ℝ)⁻¹ := by
      rw [div_le_iff₀ (by positivity)]; linarith
    gcongr
  · -- (iii) N d 4^{-p₀} ≤ 1/8
    rw [inv_pow, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    linarith
