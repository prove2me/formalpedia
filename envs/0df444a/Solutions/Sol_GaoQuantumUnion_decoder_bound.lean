-- Prove2me | solution 1 for GaoQuantumUnion.decoder_bound
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-23T06:00:07.909805+00:00
-- url     : https://prove2.me/submissions/533b7090-3000-4c00-8966-ede9a592e706

import Definitions.Def_GaoQuantumUnion_Decoding
open Matrix WildeQIT GaoQuantumUnion
open scoped MatrixOrder ComplexOrder ComplexConjugate
set_option autoImplicit false

namespace GaoDec
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

lemma operator_bound' {N : ℕ}
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

lemma rejectPrefix_eq {M : ℕ} (Q : Fin M → Matrix ι ι ℂ) (m : Fin M) :
    rejectPrefix Q m = seqOp (fun i : Fin m.val => 1 - Q ⟨i.val, lt_trans i.2 m.2⟩) := by
  unfold rejectPrefix seqOp
  congr 1
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp

lemma sum_filter_eq {M : ℕ} (f : Fin M → Matrix ι ι ℂ) (m : Fin M) :
    ∑ i : Fin m.val, f ⟨i.val, lt_trans i.2 m.2⟩
      = ∑ i ∈ Finset.univ.filter (fun i : Fin M => i.val < m.val), f i := by
  apply Finset.sum_bij (fun (i : Fin m.val) _ => (⟨i.val, lt_trans i.2 m.2⟩ : Fin M))
  · intro i _; exact Finset.mem_filter.2 ⟨Finset.mem_univ _, i.2⟩
  · intro a _ b _ h; ext; simpa using congrArg Fin.val h
  · intro b hb
    refine ⟨⟨b.val, by simpa using hb⟩, Finset.mem_univ _, rfl⟩
  · intro i _; rfl

lemma alg (P S E A : Matrix ι ι ℂ) (h : P * P = P) :
    P * Sᴴ * (S * P) - (P - (4 : ℂ) • (P * (1 - A) * P) - (4 : ℂ) • (P * E * P))
      = P * (Sᴴ * S - (1 - (4 : ℂ) • (E + (1 - A)))) * P := by
  have : P * (Sᴴ * S - (1 - (4 : ℂ) • (E + (1 - A)))) * P
      = P * Sᴴ * (S * P) - (P * P - (4 : ℂ) • (P * (1 - A) * P) - (4 : ℂ) • (P * E * P)) := by
    simp only [ofNat_smul_eq_nsmul (R := ℂ)]
    noncomm_ring
  rw [this, h]

end GaoDec

open GaoDec in
theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] {M : ℕ}
    (P : Matrix ι ι ℂ) (hP : IsProjector P) (Q : Fin M → Matrix ι ι ℂ)
    (hQ : ∀ i, IsProjector (Q i)) (m : Fin M) :
    (decoderEffect P Q m-(P-(4 : ℂ) • (P*(1-Q m)*P)-
      (4 : ℂ) • ∑ i ∈ Finset.univ.filter (fun i : Fin M => i.val < m.val), P*Q i*P)).PosSemidef := by
  set G : Fin m.val → Matrix ι ι ℂ := fun i => 1 - Q ⟨i.val, lt_trans i.2 m.2⟩ with hG
  set F : Fin (m.val + 1) → Matrix ι ι ℂ := Fin.snoc G (Q m) with hF
  have hFp : ∀ i, IsProjector (F i) := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [hF] using hQ m
    · simp only [hF, Fin.snoc_castSucc, hG]
      obtain ⟨h1, h2⟩ := hQ ⟨j.val, lt_trans j.2 m.2⟩
      refine ⟨?_, ?_⟩
      · exact (isHermitian_one).sub h1
      · rw [sub_mul, mul_sub, mul_sub, h2]; noncomm_ring
  have hop := operator_bound' F hFp
  have hS : seqOp F = Q m * rejectPrefix Q m := by
    rw [seqOp_succ, rejectPrefix_eq]
    simp [hF, hG]
  have hsum : ∑ i, (1 - F i) = ∑ i ∈ Finset.univ.filter (fun i : Fin M => i.val < m.val), Q i
      + (1 - Q m) := by
    rw [Fin.sum_univ_castSucc, ← sum_filter_eq Q m]
    simp [hF, hG]
  rw [hS, hsum] at hop
  have hc := hop.conjTranspose_mul_mul_same P
  have hPh : Pᴴ = P := hP.1
  convert hc using 1
  rw [hPh]
  unfold decoderEffect decoderK
  rw [conjTranspose_mul, hPh, mul_assoc P, ← alg P _ _ _ hP.2, Finset.mul_sum, Finset.sum_mul]
  simp only [mul_assoc]
