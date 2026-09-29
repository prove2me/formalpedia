-- Prove2me | solution 1 for ExactSDPDuality.ELSD.lemma9
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:16:28.066148+00:00
-- url     : https://prove2.me/submissions/045007f5-1f80-4657-a960-8b80161571c5

import Mathlib
import Definitions.Def_ExactSDPDuality_ELSD_Model

open Matrix

namespace ExactSDPDuality.ELSD

open scoped MatrixOrder

lemma aux_l9_frob_eq_trace {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) :
    frob A B = trace (Aᵀ * B) := by
  simp only [frob, trace, diag, mul_apply, transpose_apply]
  rw [Finset.sum_comm]

lemma aux_l9_frob_Qaff {n m : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin m → Matrix (Fin n) (Fin n) ℝ) (x : Fin m → ℝ) (M : Matrix (Fin n) (Fin n) ℝ) :
    frob (Qaff Q0 Q x) M = frob Q0 M - ∑ j, x j * frob M (Q j) := by
  simp only [frob, Qaff, Qhat, Matrix.sub_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]
  congr 1
  refine (Finset.sum_congr rfl fun a _ => Finset.sum_comm).trans ?_
  refine Finset.sum_comm.trans ?_
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun b _ => ?_
  ring

lemma aux_l9_factor {n : ℕ} {P : Matrix (Fin n) (Fin n) ℝ} (hP : P.PosSemidef) :
    ∃ B : Matrix (Fin n) (Fin n) ℝ, P = Bᴴ * B := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hP.nonneg
  exact ⟨B, hB⟩

lemma aux_l9_trace_nonneg {n : ℕ} {P D : Matrix (Fin n) (Fin n) ℝ} (hP : P.PosSemidef)
    (hD : D.PosSemidef) : 0 ≤ trace (P * D) := by
  obtain ⟨B, rfl⟩ := aux_l9_factor hP
  rw [Matrix.mul_assoc, trace_mul_comm]
  exact (hD.mul_mul_conjTranspose_same B).trace_nonneg

lemma aux_l9_mul_zero {n : ℕ} {P X : Matrix (Fin n) (Fin n) ℝ} (hP : P.PosSemidef)
    (h : trace (P * (X * Xᴴ)) = 0) : P * X = 0 := by
  obtain ⟨B, rfl⟩ := aux_l9_factor hP
  have h2 : trace ((B * X) * (B * X)ᴴ) = 0 := by
    rw [← h, conjTranspose_mul, Matrix.mul_assoc Bᴴ, trace_mul_comm Bᴴ]
    simp only [Matrix.mul_assoc]
  have := trace_mul_conjTranspose_self_eq_zero_iff.mp h2
  rw [Matrix.mul_assoc, this, Matrix.mul_zero]

lemma aux_l9_seq {n m : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin m → Matrix (Fin n) (Fin n) ℝ) (k : ℕ) (U W : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hC : IsCSeq Q0 Q k U W) (x : Fin m → ℝ) (hx : x ∈ feasibleSet Q0 Q) :
    ∀ i, i ≤ k → Qaff Q0 Q x * U i = 0 ∧ Qaff Q0 Q x * W i = 0 := by
  obtain ⟨hU0, hW0, hC⟩ := hC
  have hP : (Qaff Q0 Q x).PosSemidef := hx
  have hPsymm : (Qaff Q0 Q x)ᵀ = Qaff Q0 Q x := by
    have := hP.isHermitian.eq
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  intro i
  induction i with
  | zero => intro _; simp [hU0, hW0]
  | succ i ih =>
    intro hi
    obtain ⟨_, hWi⟩ := ih (by omega)
    obtain ⟨⟨hq0, hqs⟩, hpsd⟩ := hC (i+1) (by omega) hi
    simp only [Nat.add_sub_cancel] at hq0 hqs
    have hfrob : frob (Qaff Q0 Q x) (U (i+1) + W i) = 0 := by
      rw [aux_l9_frob_Qaff, hq0]
      have hqs' : ∀ j, frob (U (i+1) + W i) (Q j) = 0 := fun j => congrFun hqs j
      simp [hqs']
    have htrU : trace (Qaff Q0 Q x * U (i+1)) = 0 := by
      rw [aux_l9_frob_eq_trace, hPsymm, Matrix.mul_add, trace_add, hWi, trace_zero,
        add_zero] at hfrob
      exact hfrob
    have hWW : (W (i+1) * (W (i+1))ᴴ).PosSemidef := posSemidef_self_mul_conjTranspose _
    have hpsd' : (U (i+1) - W (i+1) * (W (i+1))ᴴ).PosSemidef := by
      rwa [conjTranspose_eq_transpose_of_trivial]
    have hUpsd : (U (i+1)).PosSemidef := by
      have := hpsd'.add hWW
      simpa using this
    obtain ⟨C, hC'⟩ := aux_l9_factor hUpsd
    constructor
    · have : Qaff Q0 Q x * Cᴴ = 0 :=
        aux_l9_mul_zero hP (by rw [conjTranspose_conjTranspose, ← hC']; exact htrU)
      rw [hC', ← Matrix.mul_assoc, this, Matrix.zero_mul]
    · have h1 := aux_l9_trace_nonneg hP hpsd'
      have h2 := aux_l9_trace_nonneg hP hWW
      rw [Matrix.mul_sub, trace_sub, htrU] at h1
      have h3 : trace (Qaff Q0 Q x * (W (i+1) * (W (i+1))ᴴ)) = 0 := by linarith
      exact aux_l9_mul_zero hP h3

end ExactSDPDuality.ELSD

open ExactSDPDuality.ELSD

theorem solution {n m : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hQ0 : Q0.IsSymm) (hQ : ∀ i, (Q i).IsSymm) (k : ℕ) (hk : k ≤ m) :
    (∀ x ∈ feasibleSet Q0 Q, ∀ U ∈ Uset Q0 Q k, ∀ W ∈ Wset Q0 Q k,
        Qaff Q0 Q x * U = 0 ∧ Qaff Q0 Q x * W = 0 ∧
          frob (Qaff Q0 Q x) U = 0 ∧ frob (Qaff Q0 Q x) W = 0) ∧
      ((0 : Fin m → ℝ) ∈ feasibleSet Q0 Q →
        ∀ U ∈ Uset Q0 Q k, ∀ W ∈ Wset Q0 Q k, frob Q0 U = 0 ∧ frob Q0 W = 0) := by
  have H1 : ∀ x ∈ feasibleSet Q0 Q, ∀ U ∈ Uset Q0 Q k, ∀ W ∈ Wset Q0 Q k,
      Qaff Q0 Q x * U = 0 ∧ Qaff Q0 Q x * W = 0 ∧
        frob (Qaff Q0 Q x) U = 0 ∧ frob (Qaff Q0 Q x) W = 0 := by
    intro x hx U hU W hW
    obtain ⟨U', W', hC, rfl⟩ := hU
    obtain ⟨U'', W'', hC2, rfl⟩ := hW
    have h1 := (aux_l9_seq Q0 Q k U' W' hC x hx k le_rfl).1
    have h2 := (aux_l9_seq Q0 Q k U'' W'' hC2 x hx k le_rfl).2
    have hP : (Qaff Q0 Q x).PosSemidef := hx
    have hPsymm : (Qaff Q0 Q x)ᵀ = Qaff Q0 Q x := by
      have := hP.isHermitian.eq
      rwa [conjTranspose_eq_transpose_of_trivial] at this
    refine ⟨h1, h2, ?_, ?_⟩
    · rw [aux_l9_frob_eq_trace, hPsymm, h1, trace_zero]
    · rw [aux_l9_frob_eq_trace, hPsymm, h2, trace_zero]
  refine ⟨H1, ?_⟩
  intro h0 U hU W hW
  have hQ0' : Qaff Q0 Q 0 = Q0 := by simp [Qaff, Qhat]
  have := H1 0 h0 U hU W hW
  rw [hQ0'] at this
  exact ⟨this.2.2.1, this.2.2.2⟩
