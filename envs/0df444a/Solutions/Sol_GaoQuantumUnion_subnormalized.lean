-- Prove2me | solution 1 for GaoQuantumUnion.subnormalized
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-23T06:02:36.122295+00:00
-- url     : https://prove2.me/submissions/2288e900-a56a-4ae5-a0a5-aaf055bbe191

import Definitions.Def_GaoQuantumUnion_Model
open Matrix WildeQIT GaoQuantumUnion
open scoped MatrixOrder ComplexOrder ComplexConjugate
set_option autoImplicit false

namespace GaoSub

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

end GaoSub

theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}
    (ρ : Matrix ι ι ℂ) (hρ : ρ.PosSemidef) (_htr : ρ.trace.re ≤ 1)
    (P : Fin N → Matrix ι ι ℂ) (hP : ∀ i, IsProjector (P i)) :
    ρ.trace.re-4*failureSum P ρ ≤ successProb P ρ :=
  GaoSub.main ρ hρ P hP
