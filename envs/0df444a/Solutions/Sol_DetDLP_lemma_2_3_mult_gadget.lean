-- Prove2me | solution 1 for DetDLP.lemma_2_3_mult_gadget
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T10:47:43.923973+00:00
-- url     : https://prove2.me/submissions/89bc15c7-f7c3-4f1a-affb-9854bcccebb6

import Mathlib
import Definitions.Def_DetDLP_BTN
import Theorems.Thm_DetDLP_fermat_convolution_gadget
open Finset
namespace DetDLP.Radix

private theorem word_lt {d : ℕ} (w : Fin d → Bool) : bitsToNat w < 2^d := by
  induction d with
  | zero => simp [bitsToNat]
  | succ d ih =>
    have h := ih (fun i => w i.castSucc)
    unfold bitsToNat at h ⊢
    rw [Fin.sum_univ_castSucc, pow_succ]
    simp only [Fin.val_castSucc,Fin.val_last] at h ⊢
    split_ifs <;> simp_all <;> omega

private def digit (B a i : ℕ) := a/B^i % B

private theorem place_values (a B n : ℕ) :
    (∑ i ∈ range n, digit B a i * B^i) + (a/B^n)*B^n = a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, pow_succ, ← Nat.div_div_eq_div_mul]
    have h := congrArg (fun z => z*B^n) (Nat.mod_add_div (a/B^n) B)
    dsimp [digit] at ih ⊢
    nlinarith only [ih,h]

private def coefficient (B a b L u : ℕ) : ℕ :=
  ∑ i ∈ range L, ∑ j ∈ range L, if i+j=u then digit B a i * digit B b j else 0

private theorem reconstruct (a b B L Q : ℕ) (hB : 0 < B) (ha : a < B^L) (hb : b < B^L)
    (hQ : L^2*B^2 < Q) :
    (∑ u ∈ range (2*L), (coefficient B a b L u % Q)*B^u) = a*b := by
  have upper (u : ℕ) : coefficient B a b L u < Q := by
    apply lt_of_le_of_lt _ hQ
    calc
      _ ≤ ∑ _i ∈ range L, ∑ _j ∈ range L, B*B := by
        apply sum_le_sum; intro i _
        apply sum_le_sum; intro j _
        split_ifs
        · exact Nat.mul_le_mul (Nat.mod_lt _ hB).le (Nat.mod_lt _ hB).le
        · exact Nat.zero_le _
      _ = _ := by simp; ring
  simp_rw [Nat.mod_eq_of_lt (upper _)]
  have hA := place_values a B L
  have hB' := place_values b B L
  simp only [Nat.div_eq_of_lt ha,zero_mul,add_zero] at hA
  simp only [Nat.div_eq_of_lt hb,zero_mul,add_zero] at hB'
  conv_rhs => rw [← hA,← hB',sum_mul_sum]
  simp_rw [coefficient,sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  have hij : i+j ∈ range (2*L) := by have := mem_range.mp hi; have := mem_range.mp hj; apply mem_range.mpr; omega
  simp [ite_mul,hij,pow_add]
  ring
end DetDLP.Radix

open DetDLP


open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace


theorem solution :
    ∃ (E : PrimitiveMachine) (outE : Fin E.tapeCount) (K : ℕ),
      ∀ d : ℕ, 1 ≤ d →
        ∃ (G : BipartiteMultigraph)
          (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
          (ext : Fin (4 * d) → Fin G.nE),
          G.nE < 1100 * (d + 1) ∧
          (G.maxDeg : ℝ) < 136 * ((d : ℝ) + 1) ^ ((3 : ℝ) / 4) ∧
          (G.nV : ℝ) ≤ polyBound K d ∧
          BoolBTNEntryEvaluable (countWord d) G T E outE (polyBound K d) (polyBound K d) ∧
          IsParsimonious G T ext (fun x =>
            bitsToNat (fun i : Fin d => x ⟨i.val, by omega⟩) *
            bitsToNat (fun i : Fin d => x ⟨d + i.val, by omega⟩) =
            bitsToNat (fun i : Fin (2 * d) => x ⟨2 * d + i.val, by omega⟩)) := by
  obtain ⟨E,out,K,h⟩ := fermat_convolution_gadget
  refine ⟨E,out,K,?_⟩
  intro d hd
  obtain ⟨k,L,hk,hsize,hL,G,T,ext,hedges,hdegree,hverts,heval,hpar⟩ := h d hd
  refine ⟨G,T,ext,hedges,hdegree,hverts,heval,?_⟩
  let B := 2^k
  let Q := 2^(4*k)+1
  have hB : 0 < B := pow_pos (by decide) _
  have hbnd : 2^d ≤ B^L := by dsimp [B]; rw [← pow_mul]; exact Nat.pow_le_pow_right (by decide) hsize
  have hQ : L^2*B^2 < Q := by
    have h := Nat.mul_le_mul_right (B^2) (Nat.pow_le_pow_left hL 2)
    have he : B^2*B^2 = 2^(4*k) := by rw [← pow_add]; dsimp [B]; rw [← pow_mul]; congr 1; omega
    exact Nat.lt_succ_of_le (h.trans_eq he)
  have equiv (x : Fin (4*d) → Bool) :=
    Radix.reconstruct
      (bitsToNat (fun i : Fin d => x ⟨i.val, by omega⟩))
      (bitsToNat (fun i : Fin d => x ⟨d+i.val, by omega⟩))
      B L Q hB
      ((Radix.word_lt _).trans_le hbnd) ((Radix.word_lt _).trans_le hbnd) hQ
  obtain ⟨hinj,H⟩ := hpar
  refine ⟨hinj,fun x => ?_⟩
  simpa only [Radix.coefficient,Radix.digit,B,Q] using
    (show _ from (equiv x) ▸ H x)
