-- Prove2me | solution 1 for FixedPointAA.Main.reduction_to_plane
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T02:38:33.132039+00:00
-- url     : https://prove2.me/submissions/9cba70b1-c204-46d5-b54a-1b472c0e46b9

import Mathlib
import Definitions.Def_FixedPointAA_Main_Setting

open scoped Matrix

namespace Aux_FixedPointAA_Main_reduction_to_plane

open FixedPointAA.Main Matrix

noncomputable def coefStep (c : ℂ) (α β : ℝ) (p : ℂ × ℂ) : ℂ × ℂ :=
  (-(p.1 - (1 - Complex.exp (-(α : ℂ) * Complex.I)) *
      (p.1 + (p.2 - (1 - Complex.exp ((β : ℂ) * Complex.I)) * (p.1 * c + p.2)) * star c)),
   -(p.2 - (1 - Complex.exp ((β : ℂ) * Complex.I)) * (p.1 * c + p.2)))

noncomputable def coef (c : ℂ) (α β : ℕ → ℝ) : ℕ → ℂ × ℂ
  | 0 => (1, 0)
  | j + 1 => coefStep c (α (j + 1)) (β (j + 1)) (coef c α β j)

lemma proj_apply {N : ℕ} (x v : Fin N → ℂ) :
    vecMulVec x (star x) *ᵥ v = (star x ⬝ᵥ v) • x := by
  rw [vecMulVec_mulVec, op_smul_eq_smul]

lemma G_apply {N : ℕ} (s T : Fin N → ℂ) (hs : star s ⬝ᵥ s = 1) (hT : star T ⬝ᵥ T = 1)
    (c : ℂ) (hc : star T ⬝ᵥ s = c) (α β : ℝ) (a b : ℂ) :
    G s T α β *ᵥ (a • s + b • T) =
      (coefStep c α β (a, b)).1 • s + (coefStep c α β (a, b)).2 • T := by
  have hsT : star s ⬝ᵥ T = star c := by rw [star_dotProduct, hc]
  unfold G Ss St coefStep
  rw [neg_mulVec, ← mulVec_mulVec]
  simp only [sub_mulVec, one_mulVec, smul_mulVec, proj_apply, dotProduct_add, dotProduct_smul,
    dotProduct_sub, smul_eq_mul, hs, hT, hc, hsT, mul_one]
  module

lemma seq_apply {N : ℕ} (s T : Fin N → ℂ) (hs : star s ⬝ᵥ s = 1) (hT : star T ⬝ᵥ T = 1)
    (c : ℂ) (hc : star T ⬝ᵥ s = c) (α β : ℕ → ℝ) (l : ℕ) :
    seqOp s T α β l *ᵥ s = (coef c α β l).1 • s + (coef c α β l).2 • T := by
  induction l with
  | zero => simp [seqOp, coef]
  | succ j ih =>
    rw [seqOp, ← mulVec_mulVec, ih, G_apply s T hs hT c hc]
    rfl

lemma amp_eq {N : ℕ} (s T : Fin N → ℂ) (hs : star s ⬝ᵥ s = 1) (hT : star T ⬝ᵥ T = 1)
    (c : ℂ) (hc : star T ⬝ᵥ s = c) (α β : ℕ → ℝ) (l : ℕ) :
    star T ⬝ᵥ (seqOp s T α β l *ᵥ s) = (coef c α β l).1 * c + (coef c α β l).2 := by
  rw [seq_apply s T hs hT c hc, dotProduct_add, dotProduct_smul, dotProduct_smul, hc, hT,
    smul_eq_mul, smul_eq_mul, mul_one]

end Aux_FixedPointAA_Main_reduction_to_plane

open Aux_FixedPointAA_Main_reduction_to_plane in
open FixedPointAA.Main in
theorem solution {N : ℕ} (s T : Fin N → ℂ)
    (hs : star s ⬝ᵥ s = 1) (hT : star T ⬝ᵥ T = 1)
    (lam : ℝ) (hlam : ‖star T ⬝ᵥ s‖ ^ 2 = lam) (hlam0 : 0 < lam)
    (α β : ℕ → ℝ) (l : ℕ) :
    ‖star T ⬝ᵥ (seqOp s T α β l *ᵥ s)‖ =
      ‖star tVec ⬝ᵥ (seqOp (sVec lam) tVec α β l *ᵥ sVec lam)‖ := by
  set c := star T ⬝ᵥ s with hc
  have hcpos : 0 < ‖c‖ := by
    rcases eq_or_lt_of_le (norm_nonneg c) with h | h
    · rw [← h] at hlam; simp at hlam <;> linarith
    · exact h
  have hr : Real.sqrt lam = ‖c‖ := by rw [← hlam, Real.sqrt_sq (norm_nonneg _)]
  -- Cauchy–Schwarz: lam ≤ 1
  have hlam1 : lam ≤ 1 := by
    set x : EuclideanSpace ℂ (Fin N) := WithLp.toLp 2 T
    set y : EuclideanSpace ℂ (Fin N) := WithLp.toLp 2 s
    have hxy : inner ℂ x y = c := by
      rw [EuclideanSpace.inner_eq_star_dotProduct, hc, dotProduct_comm]
    have hxx : ‖x‖ = 1 := by
      have h1 := @norm_sq_eq_re_inner ℂ _ _ _ _ x
      rw [EuclideanSpace.inner_eq_star_dotProduct] at h1
      have : WithLp.ofLp x ⬝ᵥ star (WithLp.ofLp x) = 1 := by
        rw [dotProduct_comm]; exact hT
      rw [this] at h1
      simp at h1
      rcases h1 with h | h
      · exact h
      · have := norm_nonneg x; linarith
    have hyy : ‖y‖ = 1 := by
      have h1 := @norm_sq_eq_re_inner ℂ _ _ _ _ y
      rw [EuclideanSpace.inner_eq_star_dotProduct] at h1
      have : WithLp.ofLp y ⬝ᵥ star (WithLp.ofLp y) = 1 := by
        rw [dotProduct_comm]; exact hs
      rw [this] at h1
      simp at h1
      rcases h1 with h | h
      · exact h
      · have := norm_nonneg y; linarith
    have hcs := norm_inner_le_norm (𝕜 := ℂ) x y
    rw [hxy, hxx, hyy, mul_one] at hcs
    rw [← hlam]
    nlinarith [norm_nonneg c]
  -- rotate T
  set u : ℂ := c / (‖c‖ : ℂ) with hu
  have hcne : (‖c‖ : ℂ) ≠ 0 := by exact_mod_cast hcpos.ne'
  have huu : star u * u = 1 := by
    rw [hu, star_div₀, Complex.star_def, Complex.conj_ofReal]
    rw [div_mul_div_comm, Complex.conj_mul']
    field_simp
  have huu' : u * star u = 1 := by rw [mul_comm]; exact huu
  set T' := u • T with hT'
  have hT'T' : star T' ⬝ᵥ T' = 1 := by
    rw [hT', star_smul, smul_dotProduct, dotProduct_smul, hT, smul_eq_mul, smul_eq_mul,
      mul_one]
    exact huu
  have hc' : star T' ⬝ᵥ s = ((Real.sqrt lam : ℝ) : ℂ) := by
    rw [hT', star_smul, smul_dotProduct, ← hc, hr, smul_eq_mul, hu, star_div₀,
      Complex.star_def, Complex.conj_ofReal, div_mul_eq_mul_div, Complex.conj_mul']
    field_simp
  have hvv : Matrix.vecMulVec T' (star T') = Matrix.vecMulVec T (star T) := by
    ext i j
    simp only [hT', Matrix.vecMulVec_apply, Pi.smul_apply, Pi.star_apply, star_smul, smul_eq_mul]
    linear_combination (T i * star (T j)) * huu'
  have hSt : ∀ b : ℝ, St T' b = St T b := by
    intro b
    unfold St
    rw [hvv]
  have hseq : ∀ j, seqOp s T' α β j = seqOp s T α β j := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih => simp only [seqOp, G, hSt, ih]
  have hnorm : ‖star T ⬝ᵥ (seqOp s T α β l *ᵥ s)‖ = ‖star T' ⬝ᵥ (seqOp s T' α β l *ᵥ s)‖ := by
    rw [hseq, hT', star_smul, smul_dotProduct, smul_eq_mul, norm_mul]
    have : ‖star u‖ = 1 := by
      have h := congrArg norm huu
      rw [norm_mul, norm_one, norm_star] at h
      rw [norm_star]
      nlinarith [norm_nonneg u]
    rw [this, one_mul]
  rw [hnorm, amp_eq s T' hs hT'T' _ hc' α β l]
  have hs2 : star (sVec lam) ⬝ᵥ sVec lam = 1 := by
    simp only [sVec, dotProduct, Fin.sum_univ_two, Pi.star_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith),
      Real.mul_self_sqrt hlam0.le]
    push_cast; ring
  have ht2 : star tVec ⬝ᵥ tVec = 1 := by simp [tVec, dotProduct, Fin.sum_univ_two]
  have hc2 : star tVec ⬝ᵥ sVec lam = ((Real.sqrt lam : ℝ) : ℂ) := by
    simp [tVec, sVec, dotProduct, Fin.sum_univ_two]
  rw [amp_eq (sVec lam) tVec hs2 ht2 _ hc2 α β l]
