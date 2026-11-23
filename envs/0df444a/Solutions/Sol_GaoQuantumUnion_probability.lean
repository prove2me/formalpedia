-- Prove2me | solution 1 for GaoQuantumUnion.probability
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-23T06:04:41.560472+00:00
-- url     : https://prove2.me/submissions/86630205-fdd5-463a-8517-1e3d07dec67f

import Definitions.Def_GaoQuantumUnion_Model
open Matrix WildeQIT GaoQuantumUnion
open scoped MatrixOrder ComplexOrder ComplexConjugate
set_option autoImplicit false

namespace GaoProb

variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma seqOp_succ {n : ℕ} (P : Fin (n+1) → Matrix ι ι ℂ) :
    seqOp P = P (Fin.last n) * seqOp (fun i => P i.castSucc) := by
  unfold seqOp
  rw [List.ofFn_succ', List.concat_eq_append, List.foldl_concat]

lemma invariant {N : ℕ} (P : Fin N → Matrix ι ι ℂ) (hP : ∀ i, IsProjector (P i)) :
    ((4 : ℂ) • ∑ i, (1 - P i) - 3 + 2 * seqOp P + 2 * (seqOp P)ᴴ
      - (seqOp P)ᴴ * seqOp P).PosSemidef := by
  induction N with
  | zero =>
    have h1 : seqOp P = 1 := by simp [seqOp]
    rw [h1]
    have : ((4 : ℂ) • ∑ i : Fin 0, (1 - P i) - 3 + 2 * (1 : Matrix ι ι ℂ)
        + 2 * (1 : Matrix ι ι ℂ)ᴴ - (1 : Matrix ι ι ℂ)ᴴ * 1) = 0 := by
      simp only [Finset.univ_eq_empty, Finset.sum_empty, smul_zero, conjTranspose_one, mul_one]
      norm_num
    rw [this]
    exact PosSemidef.zero
  | succ n ih =>
    have ih' := ih (fun i => P i.castSucc) (fun i => hP _)
    rw [seqOp_succ, Fin.sum_univ_castSucc]
    set K := seqOp (fun i => P i.castSucc)
    set R := P (Fin.last n)
    obtain ⟨hRh, hRR⟩ := hP (Fin.last n)
    have hRh' : Rᴴ = R := hRh
    have hRR : R * R = R := hRR
    set Q : Matrix ι ι ℂ := 1 - R with hQ
    have hQh : Qᴴ = Q := by rw [hQ, conjTranspose_sub, conjTranspose_one, hRh']
    have hQQ : Q * Q = Q := by
      rw [hQ, sub_mul, mul_sub, mul_sub, hRR]; noncomm_ring
    have hX := posSemidef_conjTranspose_mul_self (Q * (2 - K))
    have hX' : (Q * (2 - K))ᴴ * (Q * (2 - K)) = (2 - Kᴴ) * Q * (2 - K) := by
      rw [conjTranspose_mul, hQh, conjTranspose_sub]
      have : (2 : Matrix ι ι ℂ)ᴴ = 2 := by
        rw [show (2 : Matrix ι ι ℂ) = 1 + 1 by norm_num, conjTranspose_add, conjTranspose_one]
      rw [this, mul_assoc, ← mul_assoc Q Q, hQQ, mul_assoc]
    rw [hX'] at hX
    have hRK : R * K = K - Q * K := by rw [hQ, sub_mul, one_mul]; abel
    have hRKh : (R * K)ᴴ = Kᴴ - Kᴴ * Q := by
      rw [conjTranspose_mul, hRh', hQ, mul_sub, mul_one]; abel
    have hRKRK : (R * K)ᴴ * (R * K) = Kᴴ * K - Kᴴ * Q * K := by
      rw [conjTranspose_mul, hRh', mul_assoc, ← mul_assoc R R, hRR, hQ]
      noncomm_ring
    rw [hRKRK, hRKh, hRK]
    have heq : (4 : ℂ) • (∑ i : Fin n, (1 - P i.castSucc) + (1 - R)) - 3 + 2 * (K - Q * K)
        + 2 * (Kᴴ - Kᴴ * Q) - (Kᴴ * K - Kᴴ * Q * K)
        = ((4 : ℂ) • ∑ i : Fin n, (1 - P i.castSucc) - 3 + 2 * K + 2 * Kᴴ - Kᴴ * K)
          + (2 - Kᴴ) * Q * (2 - K) := by
      rw [← hQ]
      simp only [ofNat_smul_eq_nsmul (R := ℂ)]
      generalize ∑ i : Fin n, (1 - P i.castSucc) = E
      noncomm_ring
    rw [heq]
    exact ih'.add hX

theorem operator_bound {N : ℕ}
    (P : Fin N → Matrix ι ι ℂ) (hP : ∀ i, IsProjector (P i)) :
    ((seqOp P)ᴴ*seqOp P-(1-(4 : ℂ) • ∑ i, (1-P i))).PosSemidef := by
  have h1 := invariant P hP
  have h2 := posSemidef_conjTranspose_mul_self (1 - seqOp P)
  have h3 := h2.add h2
  have heq : (seqOp P)ᴴ*seqOp P-(1-(4 : ℂ) • ∑ i, (1-P i))
      = ((4 : ℂ) • ∑ i, (1 - P i) - 3 + 2 * seqOp P + 2 * (seqOp P)ᴴ
        - (seqOp P)ᴴ * seqOp P)
        + ((1 - seqOp P)ᴴ * (1 - seqOp P) + (1 - seqOp P)ᴴ * (1 - seqOp P)) := by
    rw [conjTranspose_sub, conjTranspose_one]
    simp only [ofNat_smul_eq_nsmul (R := ℂ)]
    generalize ∑ i, (1 - P i) = E
    rw [show (3 : Matrix ι ι ℂ) = 1 + 1 + 1 by norm_num]
    noncomm_ring
  rw [heq]
  exact h1.add h3

lemma trace_mul_psd_nonneg (X ρ : Matrix ι ι ℂ) (hX : X.PosSemidef) (hρ : ρ.PosSemidef) :
    0 ≤ (X * ρ).trace.re := by
  obtain ⟨C, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hX.nonneg
  rw [star_eq_conjTranspose, mul_assoc, trace_mul_comm]
  have := (hρ.mul_mul_conjTranspose_same C).trace_nonneg
  exact (Complex.nonneg_iff.mp this).1

lemma main {N : ℕ} (ρ : Matrix ι ι ℂ) (hρ : ρ.PosSemidef)
    (P : Fin N → Matrix ι ι ℂ) (hP : ∀ i, IsProjector (P i)) :
    ρ.trace.re - 4 * failureSum P ρ ≤ successProb P ρ := by
  have h := trace_mul_psd_nonneg _ ρ (operator_bound P hP) hρ
  have hs : successProb P ρ = ((seqOp P)ᴴ * seqOp P * ρ).trace.re := by
    unfold successProb seqOutput
    rw [trace_mul_cycle]
  rw [hs]
  unfold failureSum failureTerm
  rw [sub_mul, sub_mul, trace_sub, trace_sub, smul_mul, Finset.sum_mul, trace_smul,
    trace_sum, one_mul] at h
  simp only [Complex.sub_re, smul_eq_mul, Complex.mul_re, Complex.re_sum, Complex.im_sum] at h
  norm_num at h
  linarith


lemma one_sub_psd (Q : Matrix ι ι ℂ) (hQ : IsProjector Q) : (1 - Q).PosSemidef := by
  have e : (1 - Q) = (1 - Q)ᴴ * (1 - Q) := by
    rw [conjTranspose_sub, conjTranspose_one, hQ.1.eq,
      show (1 - Q) * (1 - Q) = 1 - Q - Q + Q * Q by noncomm_ring, hQ.2]
    abel
  rw [e]; exact posSemidef_conjTranspose_mul_self _

lemma failureTerm_nonneg (Q ρ : Matrix ι ι ℂ) (hQ : IsProjector Q) (hρ : ρ.PosSemidef) :
    0 ≤ failureTerm Q ρ :=
  trace_mul_psd_nonneg _ ρ (one_sub_psd Q hQ) hρ

lemma contraction {N : ℕ} (P : Fin N → Matrix ι ι ℂ) (hP : ∀ i, IsProjector (P i)) :
    (1 - (seqOp P)ᴴ * seqOp P).PosSemidef := by
  induction N with
  | zero =>
    have h1 : seqOp P = 1 := by simp [seqOp]
    rw [h1]; simpa using (PosSemidef.zero : (0 : Matrix ι ι ℂ).PosSemidef)
  | succ n ih =>
    have ih' := ih (fun i => P i.castSucc) (fun i => hP _)
    rw [seqOp_succ]
    set K := seqOp (fun i => P i.castSucc)
    set R := P (Fin.last n)
    obtain ⟨hRh, hRR⟩ := hP (Fin.last n)
    have hRh' : Rᴴ = R := hRh
    have hRR : R * R = R := hRR
    have hQQ : (1 - R) * (1 - R) = 1 - R := by
      rw [show (1 - R) * (1 - R) = 1 - R - R + R * R by noncomm_ring, hRR]; abel
    have e : 1 - (R * K)ᴴ * (R * K) = (1 - Kᴴ * K) + ((1 - R) * K)ᴴ * ((1 - R) * K) := by
      rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_sub, conjTranspose_one, hRh',
        show Kᴴ * R * (R * K) = Kᴴ * (R * R) * K by simp only [mul_assoc], hRR,
        show Kᴴ * (1 - R) * ((1 - R) * K) = Kᴴ * ((1 - R) * (1 - R)) * K by
          simp only [mul_assoc], hQQ]
      noncomm_ring
    rw [e]
    exact ih'.add (posSemidef_conjTranspose_mul_self _)

lemma re_trace_conj (K ρ : Matrix ι ι ℂ) (hρ : ρ.PosSemidef) :
    (ρ * Kᴴ).trace.re = (K * ρ).trace.re := by
  have : ρ * Kᴴ = (K * ρ)ᴴ := by rw [conjTranspose_mul, hρ.1.eq]
  rw [this, trace_conjTranspose]; simp

lemma re_trace_conj' (K ρ : Matrix ι ι ℂ) (hρ : ρ.PosSemidef) :
    (Kᴴ * ρ).trace.re = (K * ρ).trace.re := by
  rw [trace_mul_comm]; exact re_trace_conj K ρ hρ

lemma q_le {N : ℕ} (ρ : Matrix ι ι ℂ) (hρ : ρ.PosSemidef)
    (P : Fin N → Matrix ι ι ℂ) (hP : ∀ i, IsProjector (P i)) :
    successProb P ρ ≤ ρ.trace.re := by
  have h := trace_mul_psd_nonneg _ ρ (contraction P hP) hρ
  have hs : successProb P ρ = ((seqOp P)ᴴ * seqOp P * ρ).trace.re := by
    unfold successProb seqOutput
    rw [trace_mul_cycle]
  rw [hs]
  rw [sub_mul, trace_sub, one_mul, Complex.sub_re] at h
  linarith

lemma hinv {N : ℕ} (ρ : Matrix ι ι ℂ) (hρ : ρ.PosSemidef)
    (P : Fin N → Matrix ι ι ℂ) (hP : ∀ i, IsProjector (P i)) :
    0 ≤ 4 * failureSum P ρ - 3 * ρ.trace.re + 4 * (seqOp P * ρ).trace.re
      - successProb P ρ := by
  have h := trace_mul_psd_nonneg _ ρ (invariant P hP) hρ
  have hs : successProb P ρ = ((seqOp P)ᴴ * seqOp P * ρ).trace.re := by
    unfold successProb seqOutput
    rw [trace_mul_cycle]
  have hc := re_trace_conj' (seqOp P) ρ hρ
  rw [hs]
  unfold failureSum failureTerm
  rw [show (3 : Matrix ι ι ℂ) = 1 + 1 + 1 by norm_num] at h
  simp only [two_mul, sub_mul, add_mul, trace_sub, trace_add, smul_mul, Finset.sum_mul,
    trace_smul, trace_sum, one_mul, Complex.sub_re, Complex.add_re, smul_eq_mul,
    Complex.mul_re, Complex.re_sum, Complex.im_sum] at h ⊢
  norm_num at h ⊢
  rw [hc] at h
  linarith

lemma hcs {N : ℕ} (ρ : Matrix ι ι ℂ) (hρ : ρ.PosSemidef)
    (P : Fin N → Matrix ι ι ℂ) :
    (seqOp P * ρ).trace.re ^ 2 ≤ successProb P ρ +
      ((seqOp P * ρ).trace.re ^ 2) * (ρ.trace.re - 1) := by
  unfold successProb seqOutput
  set a := (seqOp P * ρ).trace.re
  set K := seqOp P
  have h := (hρ.mul_mul_conjTranspose_same (K - (a : ℂ) • 1)).trace_nonneg
  have h' := (Complex.nonneg_iff.mp h).1
  have e : (K - (a : ℂ) • 1) * ρ * (K - (a : ℂ) • 1)ᴴ
      = K * ρ * Kᴴ - (a : ℂ) • (ρ * Kᴴ) - (a : ℂ) • (K * ρ) + ((a : ℂ) * a) • ρ := by
    rw [conjTranspose_sub, conjTranspose_smul, conjTranspose_one]
    simp only [Complex.star_def, Complex.conj_ofReal, sub_mul, mul_sub, smul_mul_assoc,
      mul_smul_comm, one_mul, mul_one, smul_smul, smul_sub]
    abel
  rw [e] at h'
  simp only [trace_sub, trace_add, trace_smul, Complex.sub_re, Complex.add_re, smul_eq_mul,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] at h'
  rw [re_trace_conj K ρ hρ] at h'
  simp only [zero_mul, sub_zero, mul_zero] at h'
  nlinarith [h']

lemma main2 {N : ℕ} (ρ : Matrix ι ι ℂ) (hρ : IsDensityOperator ρ)
    (P : Fin N → Matrix ι ι ℂ) (hP : ∀ i, IsProjector (P i)) :
    1-4*failureSum P ρ ≤ successProb P ρ ∧
    (successProb P ρ=1-4*failureSum P ρ ↔ ∀ i, failureTerm (P i) ρ=0) := by
  obtain ⟨hpsd, htr⟩ := hρ
  have hT : ρ.trace.re = 1 := by rw [htr]; simp
  have h1 := GaoProb.main ρ hpsd P hP
  have h2 := q_le ρ hpsd P hP
  have h3 := hinv ρ hpsd P hP
  have h4 := hcs ρ hpsd P
  rw [hT] at h1 h2 h3 h4
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ failureTerm (P i) ρ :=
    fun i _ => failureTerm_nonneg _ _ (hP i) hpsd
  have hE0 : 0 ≤ failureSum P ρ := Finset.sum_nonneg hnn
  refine ⟨h1, ?_, ?_⟩
  · intro hq
    set a := (seqOp P * ρ).trace.re
    set q := successProb P ρ
    set E := failureSum P ρ
    have hE : E = 0 := by
      by_cases hc : 0 ≤ 1 - 2 * E
      · have ha : 1 - 2 * E ≤ a := by linarith
        have : (1 - 2 * E) ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hc ha 2
        nlinarith
      · nlinarith [sq_nonneg a]
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hE i (Finset.mem_univ _)
    exact this
  · intro hall
    have hE : failureSum P ρ = 0 := Finset.sum_eq_zero (fun i _ => hall i)
    rw [hE] at h1 ⊢
    linarith

end GaoProb

theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}
    (ρ : Matrix ι ι ℂ) (hρ : IsDensityOperator ρ)
    (P : Fin N → Matrix ι ι ℂ) (hP : ∀ i, IsProjector (P i)) :
    1-4*failureSum P ρ ≤ successProb P ρ ∧
    (successProb P ρ=1-4*failureSum P ρ ↔ ∀ i, failureTerm (P i) ρ=0) :=
  GaoProb.main2 ρ hρ P hP
