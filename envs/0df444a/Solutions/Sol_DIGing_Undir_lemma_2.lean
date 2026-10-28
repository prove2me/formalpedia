-- Prove2me | solution 1 for DIGing.Undir.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T17:53:55.32832+00:00
-- url     : https://prove2.me/submissions/f30e9aca-62dd-4a0c-8609-0537b1edde1b

import Mathlib
import Definitions.Def_DIGing_Undir_Common
import Definitions.Def_DIGing_Undir_Setting

namespace Aux_DIG_L2

open DIGing.Undir Matrix

lemma ev_sum {p n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p)) (r : Fin p) :
    (∑ i, f i) r = ∑ i, f i r := by
  simp [WithLp.ofLp_sum, Finset.sum_apply]

lemma mix_apply {n p : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (v : Stack n p) (i : Fin n) (r : Fin p) :
    mix M v i r = ∑ j, M i j * v j r := by
  unfold mix
  rw [ev_sum]
  simp

lemma frob_mix {n p : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (c : Stack n p) :
    frob (mix M c) ≤ sigmaMax M * frob c := by
  set T := Matrix.toEuclideanCLM (𝕜 := ℝ) M with hT
  let col : Fin p → EuclideanSpace ℝ (Fin n) := fun r => WithLp.toLp 2 (fun i => c i r)
  have hcol : ∀ r i, col r i = c i r := fun r i => rfl
  have hTcol : ∀ r i, T (col r) i = mix M c i r := by
    intro r i
    rw [mix_apply]
    rfl
  have h1 : ∑ i, ‖c i‖ ^ 2 = ∑ r, ‖col r‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs, hcol]
    exact Finset.sum_comm
  have h2 : ∑ i, ‖mix M c i‖ ^ 2 = ∑ r, ‖T (col r)‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs, hTcol]
    exact Finset.sum_comm
  have hσ : 0 ≤ sigmaMax M := norm_nonneg _
  have h3 : ∑ r, ‖T (col r)‖ ^ 2 ≤ sigmaMax M ^ 2 * ∑ r, ‖col r‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r _
    have := T.le_opNorm (col r)
    have h0 := norm_nonneg (T (col r))
    rw [← mul_pow]
    exact pow_le_pow_left₀ h0 this 2
  unfold frob
  rw [h2, h1]
  calc Real.sqrt (∑ r, ‖T (col r)‖ ^ 2) ≤ Real.sqrt (sigmaMax M ^ 2 * ∑ r, ‖col r‖ ^ 2) :=
        Real.sqrt_le_sqrt h3
    _ = sigmaMax M * Real.sqrt (∑ r, ‖col r‖ ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hσ]

end Aux_DIG_L2

open DIGing.Undir Matrix Aux_DIG_L2 in
theorem solution {n p : ℕ} (W : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hW : ∀ k, W k ∈ doublyStochastic ℝ (Fin n)) (B : ℕ) :
    ∀ k : ℕ, B - 1 ≤ k → ∀ b : Stack n p,
      frob (cons (mix (prodW W B k) b)) ≤ deltaK W B k * frob (cons b) := by
  intro k _ b
  set P := prodW W B k with hP
  have hPds : P ∈ doublyStochastic ℝ (Fin n) := by
    rw [hP]
    unfold prodW
    apply Submonoid.list_prod_mem
    intro x hx
    rw [List.mem_ofFn] at hx
    obtain ⟨t, rfl⟩ := hx
    split_ifs
    · exact hW _
    · exact Submonoid.one_mem _
  have hrow := sum_row_of_mem_doublyStochastic hPds
  have hcolsum := sum_col_of_mem_doublyStochastic hPds
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have : ∀ v : Stack 0 p, frob v = 0 := fun v => by simp [frob]
    rw [this, this, mul_zero]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  -- the identity cons (mix P b) = mix (P - J) (cons b)
  have hid : cons (mix P b) = mix (P - avgMat n) (cons b) := by
    funext i
    apply PiLp.ext
    intro r
    unfold cons
    simp only [Pi.sub_apply, PiLp.sub_apply, mix_apply]
    unfold ones avg
    simp only [PiLp.smul_apply, ev_sum, mix_apply, smul_eq_mul, Matrix.sub_apply, avgMat,
      Matrix.of_apply, sub_mul]
    rw [Finset.sum_sub_distrib]
    have e1 : ∑ x, ∑ j, P x j * b j r = ∑ j, b j r := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_mul, hcolsum j, one_mul]
    have e2 : ∑ j, P i j * (b j r - 1 / (n : ℝ) * ∑ x, b x r) =
        ∑ j, P i j * b j r - 1 / (n : ℝ) * ∑ x, b x r := by
      simp only [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hrow i, one_mul]
    have e3 : ∑ j, 1 / (n : ℝ) * (b j r - 1 / (n : ℝ) * ∑ x, b x r) = 0 := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      field_simp
      ring
    rw [e1, e2, e3]
    ring
  rw [hid]
  exact frob_mix _ _
