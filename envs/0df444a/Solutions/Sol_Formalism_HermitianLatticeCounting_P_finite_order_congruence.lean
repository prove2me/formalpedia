-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.finite_order_congruence
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:46.685321+00:00
-- url     : https://prove2.me/submissions/9d2cba1a-9246-4721-bf86-41df20ca0517

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_HyperbolicPlaceProducts_ArithmeticCountRevised
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IdealsOfNormEqIndexSet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
namespace Formalism.HermitianLatticeCounting.P
private theorem fo_step_lemma (N p q s : ℕ) (hp : p.Prime) (hq : q.Prime) (hs : 1 ≤ s)
    (hps : 2 ≤ (p - 1) * s) (Y : Matrix (Fin N) (Fin N) ℤ)
    (h : (1 + ((p : ℤ) ^ s) • Y) ^ q = 1) : ∃ W : Matrix (Fin N) (Fin N) ℤ, Y = (p : ℤ) • W := by
  set X := ((p : ℤ) ^ s) • Y with hX
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero

  have hbin : (X + 1) ^ q = ∑ m ∈ Finset.range (q + 1), X ^ m * (q.choose m : Matrix (Fin N) (Fin N) ℤ) := by
    rw [(Commute.one_right X).add_pow]; simp
  have hq2 := hq.two_le
  have hsplit : ∑ m ∈ Finset.range (q + 1), X ^ m * (q.choose m : Matrix (Fin N) (Fin N) ℤ) =
      1 + (q : ℤ) • X + ∑ m ∈ Finset.range (q - 1),
        (((p : ℤ) ^ s) ^ (m + 2) * (q.choose (m + 2) : ℤ)) • Y ^ (m + 2) := by
    have e : q + 1 = (q - 1) + 1 + 1 := by omega
    rw [e, Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, zero_add, pow_one,
      Nat.choose_one_right]
    have e2 : ∀ m, X ^ (m + 1 + 1) * (q.choose (m + 1 + 1) : Matrix (Fin N) (Fin N) ℤ) =
        (((p : ℤ) ^ s) ^ (m + 2) * (q.choose (m + 2) : ℤ)) • Y ^ (m + 2) := by
      intro m
      rw [hX, smul_pow, ← nsmul_eq_mul', ← Nat.cast_smul_eq_nsmul ℤ, smul_smul, mul_comm]
    simp only [e2]
    rw [← nsmul_eq_mul', ← Nat.cast_smul_eq_nsmul ℤ]
    abel
  have hmain : (q : ℤ) • X = -∑ m ∈ Finset.range (q - 1),
      (((p : ℤ) ^ s) ^ (m + 2) * (q.choose (m + 2) : ℤ)) • Y ^ (m + 2) := by
    have := h
    rw [add_comm, hbin, hsplit] at this
    rw [eq_neg_iff_add_eq_zero]
    have h2 := congrArg (· - 1) this
    simp only [add_sub_cancel_left, sub_self] at h2
    rw [← h2]; abel
  by_cases hqp : q = p
  · subst hqp

    have hterm : ∀ m ∈ Finset.range (q - 1),
        ((q : ℤ) ^ (s + 2)) ∣ ((q : ℤ) ^ s) ^ (m + 2) * (q.choose (m + 2) : ℤ) := by
      intro m hm
      rw [Finset.mem_range] at hm
      rw [← pow_mul]
      by_cases hlt : m + 2 < q
      · have hc : (q : ℤ) ∣ (q.choose (m + 2) : ℤ) := by
          exact_mod_cast hq.dvd_choose_self (by omega) hlt
        have : (q : ℤ) ^ (s + 2) ∣ (q : ℤ) ^ (s * (m + 2)) * q := by
          rw [← pow_succ]; exact pow_dvd_pow _ (by nlinarith)
        exact this.trans (mul_dvd_mul_left _ hc)
      · have hm2 : m + 2 = q := by omega
        rw [hm2]
        apply Dvd.dvd.mul_right
        apply pow_dvd_pow
        have : (q - 1) * s ≤ s * q - s := by
          rw [Nat.sub_mul, one_mul, mul_comm]
        omega
    choose c hc using hterm
    have hsum : ∑ m ∈ Finset.range (q - 1),
        (((q : ℤ) ^ s) ^ (m + 2) * (q.choose (m + 2) : ℤ)) • Y ^ (m + 2) =
        ((q : ℤ) ^ (s + 2)) • ∑ m ∈ (Finset.range (q - 1)).attach, c m.1 m.2 • Y ^ (m.1 + 2) := by
      rw [Finset.smul_sum, ← Finset.sum_attach]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [hc m.1 m.2, smul_smul]
    rw [hsum, hX, smul_smul, ← smul_neg] at hmain
    have e1 : (q : ℤ) * (q : ℤ) ^ s = (q : ℤ) ^ (s + 1) := by ring
    have e2 : (q : ℤ) ^ (s + 2) = (q : ℤ) ^ (s + 1) * q := by ring
    rw [e1, e2, ← smul_smul] at hmain
    refine ⟨_, smul_right_injective _ (pow_ne_zero _ hp0) hmain⟩
  ·
    have hterm : ∀ m ∈ Finset.range (q - 1),
        ((p : ℤ) ^ (2 * s)) ∣ ((p : ℤ) ^ s) ^ (m + 2) * (q.choose (m + 2) : ℤ) := by
      intro m _
      rw [← pow_mul]
      exact Dvd.dvd.mul_right (pow_dvd_pow _ (by nlinarith)) _
    choose c hc using hterm
    have hsum : ∑ m ∈ Finset.range (q - 1),
        (((p : ℤ) ^ s) ^ (m + 2) * (q.choose (m + 2) : ℤ)) • Y ^ (m + 2) =
        ((p : ℤ) ^ (2 * s)) • ∑ m ∈ (Finset.range (q - 1)).attach, c m.1 m.2 • Y ^ (m.1 + 2) := by
      rw [Finset.smul_sum, ← Finset.sum_attach]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [hc m.1 m.2, smul_smul]
    rw [hsum, hX, smul_comm, ← smul_neg, two_mul, pow_add, ← smul_smul] at hmain
    obtain ⟨W', hqY⟩ : ∃ W' : Matrix (Fin N) (Fin N) ℤ, (q : ℤ) • Y = ((p : ℤ) ^ s) • W' :=
      ⟨_, smul_right_injective _ (pow_ne_zero s hp0) hmain⟩
    have hcop : IsCoprime (q : ℤ) ((p : ℤ) ^ s) := by
      apply IsCoprime.pow_right
      rw [Nat.isCoprime_iff_coprime]
      exact (Nat.coprime_primes hq hp).2 hqp
    obtain ⟨a, b, hab⟩ := hcop
    refine ⟨(p : ℤ) ^ (s - 1) • (a • W' + b • Y), ?_⟩
    calc Y = (a * q + (p : ℤ) ^ s * b) • Y := by
          rw [show a * (q : ℤ) + (p : ℤ) ^ s * b = 1 by linear_combination hab, one_smul]
      _ = a • ((q : ℤ) • Y) + ((p : ℤ) ^ s) • (b • Y) := by rw [add_smul, smul_smul, smul_smul]
      _ = a • (((p : ℤ) ^ s) • W') + ((p : ℤ) ^ s) • (b • Y) := by rw [hqY]
      _ = ((p : ℤ) ^ s) • (a • W' + b • Y) := by rw [smul_add, smul_comm a]
      _ = (p : ℤ) • ((p : ℤ) ^ (s - 1) • (a • W' + b • Y)) := by
          rw [smul_smul, ← pow_succ', Nat.sub_add_cancel hs]
private theorem fo_zero_lemma_2 (N p q s0 : ℕ) (hp : p.Prime) (hq : q.Prime) (hs0 : 1 ≤ s0)
    (hps : 2 ≤ (p - 1) * s0) (A : Matrix (Fin N) (Fin N) ℤ) (hA : A ^ q = 1)
    (h0 : ∃ Y : Matrix (Fin N) (Fin N) ℤ, A = 1 + ((p : ℤ) ^ s0) • Y) : A = 1 := by
  have hall : ∀ k : ℕ, ∃ Y : Matrix (Fin N) (Fin N) ℤ, A = 1 + ((p : ℤ) ^ (s0 + k)) • Y := by
    intro k
    induction k with
    | zero => simpa using h0
    | succ k ih =>
      obtain ⟨Y, hY⟩ := ih
      obtain ⟨W, hW⟩ := fo_step_lemma N p q (s0 + k) hp hq (by omega)
        (le_trans hps (Nat.mul_le_mul_left _ (by omega))) Y (hY ▸ hA)
      refine ⟨W, ?_⟩
      rw [hY, hW, smul_smul, ← pow_succ, ← add_assoc]
  ext i j
  have hdv : ∀ k : ℕ, ((p : ℤ) ^ k) ∣ (A i j - (1 : Matrix (Fin N) (Fin N) ℤ) i j) := by
    intro k
    obtain ⟨Y, hY⟩ := hall k
    have : A i j - (1 : Matrix (Fin N) (Fin N) ℤ) i j = (p : ℤ) ^ (s0 + k) * Y i j := by
      rw [hY, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; ring
    rw [this]
    exact (pow_dvd_pow _ (by omega)).trans (dvd_mul_right _ _)
  set e := A i j - (1 : Matrix (Fin N) (Fin N) ℤ) i j
  have : e = 0 := by
    apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (hdv e.natAbs)
    rw [Int.natAbs_pow, Int.natAbs_natCast]
    exact Nat.lt_pow_self hp.one_lt
  linarith
open Formalism.SLP.P.CountO NumberField
open scoped nonZeroDivisors
open NumberField Formalism.SLP.P.CountO
end Formalism.HermitianLatticeCounting.P
end

set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : FiniteOrderCongruence := by
  intro N n g A B hg hn hA hAB
  by_contra hne

  have hpow : ∀ k : ℕ, ∃ C : Matrix (Fin N) (Fin N) ℤ, A ^ k = 1 + g • C := by
    intro k
    induction k with
    | zero => exact ⟨0, by simp⟩
    | succ k ih =>
      obtain ⟨C, hC⟩ := ih
      refine ⟨C + B + g • (C * B), ?_⟩
      rw [pow_succ, hC, hAB]
      simp only [smul_add, mul_add, add_mul, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
        smul_smul]
      abel

  have hfin : IsOfFinOrder A := isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, hA⟩
  have ho : orderOf A ≠ 1 := by rw [Ne, orderOf_eq_one_iff]; exact hne
  obtain ⟨q, hq, hqo⟩ := Nat.exists_prime_and_dvd ho
  have hopos := hfin.orderOf_pos
  set A' := A ^ (orderOf A / q) with hA'
  have hA'q : A' ^ q = 1 := by
    rw [hA', ← pow_mul, Nat.div_mul_cancel hqo, pow_orderOf_eq_one]
  have hA'ne : A' ≠ 1 := by
    apply pow_ne_one_of_lt_orderOf
    · exact (Nat.div_pos (Nat.le_of_dvd hopos hqo) hq.pos).ne'
    · exact Nat.div_lt_self hopos hq.one_lt
  obtain ⟨C, hC⟩ := hpow (orderOf A / q)
  rw [← hA'] at hC

  obtain ⟨G, rfl⟩ : ∃ G : ℕ, g = (G : ℤ) := ⟨g.toNat, by omega⟩
  have hG : 3 ≤ G := by exact_mod_cast hg
  have key : ∃ p s0 : ℕ, p.Prime ∧ 1 ≤ s0 ∧ 2 ≤ (p - 1) * s0 ∧ p ^ s0 ∣ G := by
    by_cases h4 : 4 ∣ G
    · exact ⟨2, 2, Nat.prime_two, by norm_num, by norm_num, by simpa using h4⟩
    · obtain ⟨H, hH, hHodd, hH3⟩ : ∃ H, H ∣ G ∧ ¬ 2 ∣ H ∧ 3 ≤ H := by
        by_cases h2 : 2 ∣ G
        · obtain ⟨h, rfl⟩ := h2
          refine ⟨h, dvd_mul_left h 2, ?_, ?_⟩
          · rintro ⟨k, rfl⟩; exact h4 ⟨k, by ring⟩
          · by_contra hlt
            interval_cases h <;> simp_all
        · exact ⟨G, dvd_rfl, h2, hG⟩
      have hpH := Nat.minFac_dvd H
      have hp := Nat.minFac_prime (show H ≠ 1 by omega)
      have hp2 : H.minFac ≠ 2 := by
        intro h; rw [h] at hpH; exact hHodd hpH
      have hp3 : 3 ≤ H.minFac := by have := hp.two_le; omega
      exact ⟨H.minFac, 1, hp, le_rfl, by omega, by simpa using hpH.trans hH⟩
  obtain ⟨p, s0, hp, hs0, hps, hdvd⟩ := key
  obtain ⟨G', hG'⟩ := hdvd
  have hform : A' = 1 + ((p : ℤ) ^ s0) • ((G' : ℤ) • C) := by
    rw [hC, smul_smul, hG']; push_cast; ring_nf
  exact hA'ne (fo_zero_lemma_2 N p q s0 hp hq hs0 hps A' hA'q ⟨_, hform⟩)
end Formalism.HermitianLatticeCounting.P
