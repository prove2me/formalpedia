-- Prove2me | solution 1 for ExactSDPDuality.ELSD.weak_duality
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:03:50.461501+00:00
-- url     : https://prove2.me/submissions/62199ebb-409c-446b-a29e-36ee77f40028

import Mathlib
import Definitions.Def_ExactSDPDuality_ELSD_Model

open Matrix

namespace ExactSDPDuality.ELSD

open scoped MatrixOrder

lemma aux_wd_frob_eq_trace {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) :
    frob A B = trace (A * Bᵀ) := by
  simp [frob, Matrix.trace, Matrix.mul_apply]

lemma aux_wd_frob_comm {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) :
    frob A B = frob B A := by
  unfold frob; simp [mul_comm]

lemma aux_wd_frob_add_left {n : ℕ} (A B C : Matrix (Fin n) (Fin n) ℝ) :
    frob (A + B) C = frob A C + frob B C := by
  unfold frob; simp [add_mul, Finset.sum_add_distrib]

lemma aux_wd_frob_sub_right {n : ℕ} (A B C : Matrix (Fin n) (Fin n) ℝ) :
    frob A (B - C) = frob A B - frob A C := by
  unfold frob; simp [mul_sub, Finset.sum_sub_distrib]

lemma aux_wd_frob_Qhat {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin m → Matrix (Fin n) (Fin n) ℝ) (x : Fin m → ℝ) :
    frob A (Qhat Q x) = ∑ l, x l * frob A (Q l) := by
  unfold frob Qhat
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  have h : ∀ a, ∑ b, ∑ l, A a b * (x l * Q l a b) = ∑ l, ∑ b, x l * (A a b * Q l a b) :=
    fun a => by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun b _ => by ring
  rw [Finset.sum_congr rfl fun a _ => h a]
  exact Finset.sum_comm

lemma aux_wd_trace_mul_nonneg {n : ℕ} {P Y : Matrix (Fin n) (Fin n) ℝ}
    (hP : P.PosSemidef) (hY : Y.PosSemidef) : 0 ≤ trace (P * Y) := by
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hY.nonneg
  rw [star_eq_conjTranspose, ← Matrix.mul_assoc, Matrix.trace_mul_cycle]
  exact (hP.mul_mul_conjTranspose_same B).trace_nonneg

lemma aux_wd_mul_eq_zero {n : ℕ} {U V Y : Matrix (Fin n) (Fin n) ℝ} (hY : Y.PosSemidef)
    (hUV : (U - V * Vᵀ).PosSemidef) (h0 : trace (U * Y) = 0) : Y * V = 0 := by
  have hVV : (V * Vᵀ).PosSemidef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using posSemidef_self_mul_conjTranspose V
  have h1 := aux_wd_trace_mul_nonneg hUV hY
  have h2 := aux_wd_trace_mul_nonneg hVV hY
  have hsum : trace ((U - V * Vᵀ) * Y) + trace ((V * Vᵀ) * Y) = trace (U * Y) := by
    rw [← trace_add, ← Matrix.add_mul, sub_add_cancel]
  have h3 : trace ((V * Vᵀ) * Y) = 0 := by linarith
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hY.nonneg
  have h4 : trace ((B * V) * (B * V)ᴴ) = 0 := by
    rw [← h3, conjTranspose_mul, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial,
      conjTranspose_eq_transpose_of_trivial]
    rw [show B * V * (Vᵀ * Bᵀ) = B * (V * Vᵀ * Bᵀ) by simp [Matrix.mul_assoc], trace_mul_comm]
    simp [Matrix.mul_assoc]
  have h5 : B * V = 0 := trace_mul_conjTranspose_self_eq_zero_iff.mp h4
  rw [Matrix.mul_assoc, h5, Matrix.mul_zero]

lemma aux_wd_symm {n : ℕ} {Y : Matrix (Fin n) (Fin n) ℝ} (hY : Y.PosSemidef) : Yᵀ = Y := by
  have := hY.1.eq
  simpa [conjTranspose_eq_transpose_of_trivial] using this

lemma aux_wd_seq {n m : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin m → Matrix (Fin n) (Fin n) ℝ) (x : Fin m → ℝ) (hx : x ∈ feasibleSet Q0 Q)
    (k : ℕ) (U W : ℕ → Matrix (Fin n) (Fin n) ℝ) (hC : IsCSeq Q0 Q k U W) :
    ∀ i, i ≤ k → Qaff Q0 Q x * W i = 0 := by
  obtain ⟨_, hW0, hstep⟩ := hC
  have hY : (Qaff Q0 Q x).PosSemidef := hx
  have hYt := aux_wd_symm hY
  intro i
  induction i with
  | zero => intro _; rw [hW0, Matrix.mul_zero]
  | succ i ih =>
    intro hi
    have hprev := ih (by omega)
    obtain ⟨⟨hq0, hqs⟩, hpsd⟩ := hstep (i+1) (by omega) hi
    simp only [Nat.add_sub_cancel] at hq0 hqs
    have hf : frob (U (i+1) + W i) (Qaff Q0 Q x) = 0 := by
      unfold Qaff
      rw [aux_wd_frob_sub_right, aux_wd_frob_Qhat, aux_wd_frob_comm, hq0]
      have : ∀ j, frob (U (i+1) + W i) (Q j) = 0 := fun j => congrFun hqs j
      simp [this]
    have hWY : frob (W i) (Qaff Q0 Q x) = 0 := by
      rw [aux_wd_frob_eq_trace, hYt, trace_mul_comm, hprev, trace_zero]
    have hUY : trace (U (i+1) * Qaff Q0 Q x) = 0 := by
      rw [aux_wd_frob_add_left, hWY, add_zero, aux_wd_frob_eq_trace, hYt] at hf
      exact hf
    exact aux_wd_mul_eq_zero hY hpsd hUY

end ExactSDPDuality.ELSD

open ExactSDPDuality.ELSD
open Matrix

theorem solution {n m : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin m → Matrix (Fin n) (Fin n) ℝ) (c : Fin m → ℝ)
    (hQ0 : Q0.IsSymm) (hQ : ∀ i, (Q i).IsSymm) (k : ℕ) (hk : k ≤ m)
    (x : Fin m → ℝ) (hx : x ∈ feasibleSet Q0 Q)
    (U W : Matrix (Fin n) (Fin n) ℝ) (hc : Qstar Q (U + W) = c)
    (hW : W ∈ Wset Q0 Q k) (hU : U.PosSemidef) :
    c ⬝ᵥ x ≤ frob (U + W) Q0 := by
  obtain ⟨Us, Ws, hC, hWk⟩ := hW
  have hY : (Qaff Q0 Q x).PosSemidef := hx
  have hYt := aux_wd_symm hY
  have hYW : Qaff Q0 Q x * W = 0 := hWk ▸ aux_wd_seq Q0 Q x hx k Us Ws hC k le_rfl
  have hWY : frob W (Qaff Q0 Q x) = 0 := by
    rw [aux_wd_frob_eq_trace, hYt, trace_mul_comm, hYW, trace_zero]
  have hUY : 0 ≤ frob U (Qaff Q0 Q x) := by
    rw [aux_wd_frob_eq_trace, hYt]
    exact aux_wd_trace_mul_nonneg hU hY
  have hcx : c ⬝ᵥ x = ∑ l, x l * frob (U + W) (Q l) := by
    rw [← hc]
    simp only [dotProduct, Qstar]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  have key : frob (U + W) (Qaff Q0 Q x) = frob (U + W) Q0 - c ⬝ᵥ x := by
    unfold Qaff
    rw [aux_wd_frob_sub_right, aux_wd_frob_Qhat, hcx]
  rw [aux_wd_frob_add_left, hWY, add_zero] at key
  linarith
