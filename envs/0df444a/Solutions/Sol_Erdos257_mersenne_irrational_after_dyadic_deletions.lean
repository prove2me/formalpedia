-- Prove2me | solution 1 for Erdos257.mersenne_irrational_after_dyadic_deletions
-- status  : ACCEPTED   (prove)
-- author  : @Mceppaglia
-- created : 2026-11-20T17:11:02.639164+00:00
-- url     : https://prove2.me/submissions/727ce194-1368-4e36-be00-701a6dc58526

import Mathlib

/-!
# Irrationality after deleting arbitrary power-of-two exponents

Matt directed this restricted Erdős #257 investigation. OpenAI Codex assisted
in developing the argument, formalizing it, and checking the proof.
The full-series divisor argument goes back to Paul Erdős (1948).
The first section includes six declarations from Will Cook's Apache-2.0 Lean
project. Source, line ranges and changes appear there; its license appears below.
-/

section

/-
Source: Will Cook, Erdos249257/CertificateKernel.lean, Apache-2.0. The license is reproduced at the end of this file.
Upstream commit 5411c40344eeb0371a5f34eafc9b22f6b4499017.
The declarations below are selected and regrouped with their original statement and proof
bodies preserved verbatim. The module uses the project’s pinned mathlib import.

Original source lines at this immutable revision:
  bpow_dvd_card_divisors_of_exact_prime_block (6505–6519)
  factorization_eq_of_modEq_prod_pow (6963–7011)
  exists_bertrand_prime_block (7696–7726)
  exists_bounded_disjoint_prime_blocks (7733–7825)
  exists_bounded_crt_residue (7831–7878)
  exists_bounded_first_block_frame (7886–8023)
https://github.com/wcook04/plectis-erdos-lean/blob/5411c40344eeb0371a5f34eafc9b22f6b4499017/Erdos249257/CertificateKernel.lean
-/

namespace Erdos249257

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

theorem bpow_dvd_card_divisors_of_exact_prime_block (b n : ℕ) (hb : 2 ≤ b) (hn : n ≠ 0)
    (P : Finset ℕ) (hexact : ∀ p ∈ P, n.factorization p = b - 1) :
    b ^ P.card ∣ n.divisors.card := by
  have hsub : P ⊆ n.primeFactors := by
    intro p hp
    rw [← Nat.support_factorization, Finsupp.mem_support_iff, hexact p hp]
    omega
  have h1 : ∀ p ∈ P, n.factorization p + 1 = b := by
    intro p hp
    rw [hexact p hp]
    omega
  have hval : ∏ p ∈ P, (n.factorization p + 1) = b ^ P.card := by
    rw [Finset.prod_congr rfl h1, Finset.prod_const]
  rw [Nat.card_divisors hn, ← hval]
  exact Finset.prod_dvd_prod_of_subset P n.primeFactors _ hsub

theorem factorization_eq_of_modEq_prod_pow
    (b : ℕ) (hb : 2 ≤ b) (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (hπ : 2 ≤ ∏ p ∈ P, p) (n : ℕ)
    (hmod : n ≡ (∏ p ∈ P, p) ^ (b - 1) [MOD (∏ p ∈ P, p) ^ b]) :
    ∀ p ∈ P, n.factorization p = b - 1 := by
  intro p hpP
  set π : ℕ := ∏ p ∈ P, p with hπdef
  have hb1 : b - 1 + 1 = b := by omega
  have hπpos : 0 < π := by omega
  have hπpow : π ^ b = π ^ (b - 1) * π := by
    calc π ^ b = π ^ (b - 1 + 1) := by rw [hb1]
      _ = π ^ (b - 1) * π := pow_succ π (b - 1)
  have hpowpos : 0 < π ^ (b - 1) := pow_pos hπpos _
  have hlt : π ^ (b - 1) < π ^ b := by
    rw [hπpow]
    exact (Nat.lt_mul_iff_one_lt_right hpowpos).mpr (by omega)
  have hmodeq : n % π ^ b = π ^ (b - 1) := by
    have h : n % π ^ b = π ^ (b - 1) % π ^ b := hmod
    rw [h, Nat.mod_eq_of_lt hlt]
  have hn_eq : n = π ^ (b - 1) * (π * (n / π ^ b) + 1) := by
    have hdm := Nat.div_add_mod n (π ^ b)
    rw [hmodeq] at hdm
    calc n = π ^ b * (n / π ^ b) + π ^ (b - 1) := hdm.symm
      _ = π ^ (b - 1) * (π * (n / π ^ b) + 1) := by rw [hπpow]; ring
  have hp := hP p hpP
  have hp_dvd_π : p ∣ π := Finset.dvd_prod_of_mem _ hpP
  have hcof_ne : π * (n / π ^ b) + 1 ≠ 0 := by omega
  have hp_ndvd : ¬ p ∣ (π * (n / π ^ b) + 1) := by
    intro hdvd
    have h1 : p ∣ π * (n / π ^ b) := hp_dvd_π.mul_right _
    have h2 : p ∣ 1 := (Nat.dvd_add_right h1).mp hdvd
    have h3 := Nat.le_of_dvd one_pos h2
    have h4 := hp.two_le
    omega
  have hvπ : π.factorization p = 1 := by
    rw [hπdef, Nat.factorization_prod (fun q hq => (hP q hq).pos.ne')]
    rw [Finset.sum_apply']
    rw [Finset.sum_eq_single p]
    · rw [(hP p hpP).factorization]
      simp
    · intro q hq hqp
      rw [(hP q hq).factorization]
      exact Finsupp.single_eq_of_ne (Ne.symm hqp)
    · intro hnot
      exact absurd hpP hnot
  have hv1 : (π * (n / π ^ b) + 1).factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hp_ndvd
  rw [hn_eq, Nat.factorization_mul (pow_pos hπpos _).ne' hcof_ne, Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hvπ, hv1, mul_one, add_zero]

theorem exists_bertrand_prime_block (m r : ℕ) (hm : 1 ≤ m) :
    ∃ Q : Finset ℕ, Q.card = r ∧ (∀ p ∈ Q, Nat.Prime p) ∧
      (∀ p ∈ Q, m < p) ∧ (∀ p ∈ Q, p ≤ 2 ^ r * m) := by
  induction r with
  | zero => exact ⟨∅, by simp, by simp, by simp, by simp⟩
  | succ r ih =>
      obtain ⟨Q, hcard, hprime, hgt, hle⟩ := ih
      have hn0 : 2 ^ r * m ≠ 0 := by positivity
      obtain ⟨p, hp, hpgt, hple⟩ := Nat.exists_prime_lt_and_le_two_mul (2 ^ r * m) hn0
      have hpnotin : p ∉ Q := fun hmem => absurd (hle p hmem) (not_le.mpr hpgt)
      refine ⟨insert p Q, ?_, ?_, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hpnotin, hcard]
      · intro x hx
        rcases Finset.mem_insert.mp hx with h | h
        · exact h ▸ hp
        · exact hprime x h
      · intro x hx
        rcases Finset.mem_insert.mp hx with h | h
        · have h1 : m ≤ 2 ^ r * m := Nat.le_mul_of_pos_left m (pow_pos (by norm_num) r)
          omega
        · exact hgt x h
      · intro x hx
        rcases Finset.mem_insert.mp hx with h | h
        · have h2 : 2 * (2 ^ r * m) = 2 ^ (r + 1) * m := by rw [pow_succ]; ring
          omega
        · have h3 : 2 ^ r * m ≤ 2 ^ (r + 1) * m := by
            have h4 : (2 : ℕ) ^ r ≤ 2 ^ (r + 1) :=
              Nat.pow_le_pow_right (by norm_num) (by omega)
            exact Nat.mul_le_mul_right m h4
          have := hle x h
          omega

theorem exists_bounded_disjoint_prime_blocks (L K : ℕ) :
    ∃ (P : ℕ → Finset ℕ) (m : ℕ),
      L + 1 ≤ m ∧ m ≤ 2 ^ (K * (K + 1)) * (L + 1) ∧
      (∀ r ∈ Finset.Icc 1 K, (P r).card = r) ∧
      (∀ r ∈ Finset.Icc 1 K, ∀ p ∈ P r, Nat.Prime p) ∧
      (∀ r ∈ Finset.Icc 1 K, ∀ p ∈ P r, L < p) ∧
      (∀ r ∈ Finset.Icc 1 K, ∀ p ∈ P r, p ≤ m) ∧
      (∀ r s, r ∈ Finset.Icc 1 K → s ∈ Finset.Icc 1 K → r ≠ s →
        Disjoint (P r) (P s)) := by
  induction K with
  | zero =>
      refine ⟨fun _ => ∅, L + 1, le_refl _, by simp, ?_, ?_, ?_, ?_, ?_⟩
      · intro r hr; exact absurd (Finset.mem_Icc.mp hr) (by omega)
      · intro r hr; exact absurd (Finset.mem_Icc.mp hr) (by omega)
      · intro r hr; exact absurd (Finset.mem_Icc.mp hr) (by omega)
      · intro r hr; exact absurd (Finset.mem_Icc.mp hr) (by omega)
      · intro r s hr hs hrs; exact absurd (Finset.mem_Icc.mp hr) (by omega)
  | succ K ih =>
      obtain ⟨P, m, hLm, hmB, hcards, hprimes, hgtL, hlem, hdisj⟩ := ih
      obtain ⟨Q, hQcard, hQprime, hQgt, hQle⟩ :=
        exists_bertrand_prime_block m (K + 1) (by omega)
      refine ⟨fun r => if r = K + 1 then Q else P r, 2 ^ (K + 1) * m,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · have h1 : m ≤ 2 ^ (K + 1) * m :=
          Nat.le_mul_of_pos_left m (pow_pos (by norm_num) _)
        omega
      · calc 2 ^ (K + 1) * m
            ≤ 2 ^ (K + 1) * (2 ^ (K * (K + 1)) * (L + 1)) :=
              Nat.mul_le_mul_left _ hmB
          _ = 2 ^ ((K + 1) + K * (K + 1)) * (L + 1) := by
              rw [← mul_assoc, ← pow_add]
          _ ≤ 2 ^ ((K + 1) * (K + 1 + 1)) * (L + 1) := by
              have h5 : (K + 1) * (K + 1 + 1)
                  = ((K + 1) + K * (K + 1)) + (K + 1) := by ring
              have h6 : (K + 1) + K * (K + 1) ≤ (K + 1) * (K + 1 + 1) := by omega
              exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) h6)
      · intro r hr
        dsimp only
        rcases Finset.mem_Icc.mp hr with ⟨hr1, hr2⟩
        by_cases h : r = K + 1
        · rw [if_pos h, hQcard, h]
        · rw [if_neg h]
          exact hcards r (Finset.mem_Icc.mpr ⟨hr1, by omega⟩)
      · intro r hr p hp
        dsimp only at hp
        rcases Finset.mem_Icc.mp hr with ⟨hr1, hr2⟩
        by_cases h : r = K + 1
        · rw [if_pos h] at hp
          exact hQprime p hp
        · rw [if_neg h] at hp
          exact hprimes r (Finset.mem_Icc.mpr ⟨hr1, by omega⟩) p hp
      · intro r hr p hp
        dsimp only at hp
        rcases Finset.mem_Icc.mp hr with ⟨hr1, hr2⟩
        by_cases h : r = K + 1
        · rw [if_pos h] at hp
          have := hQgt p hp
          omega
        · rw [if_neg h] at hp
          exact hgtL r (Finset.mem_Icc.mpr ⟨hr1, by omega⟩) p hp
      · intro r hr p hp
        dsimp only at hp
        rcases Finset.mem_Icc.mp hr with ⟨hr1, hr2⟩
        by_cases h : r = K + 1
        · rw [if_pos h] at hp
          have h1 : 2 ^ (K + 1) = 2 ^ (K + 1) := rfl
          exact hQle p hp
        · rw [if_neg h] at hp
          have h1 : p ≤ m := hlem r (Finset.mem_Icc.mpr ⟨hr1, by omega⟩) p hp
          have h2 : m ≤ 2 ^ (K + 1) * m :=
            Nat.le_mul_of_pos_left m (pow_pos (by norm_num) _)
          omega
      · intro r s hr hs hrs
        dsimp only
        rcases Finset.mem_Icc.mp hr with ⟨hr1, hr2⟩
        rcases Finset.mem_Icc.mp hs with ⟨hs1, hs2⟩
        by_cases h1 : r = K + 1
        · have h2 : ¬ s = K + 1 := by omega
          rw [if_pos h1, if_neg h2, Finset.disjoint_left]
          intro p hpQ hpPs
          have hgt := hQgt p hpQ
          have hle := hlem s (Finset.mem_Icc.mpr ⟨hs1, by omega⟩) p hpPs
          omega
        · rw [if_neg h1]
          by_cases h2 : s = K + 1
          · rw [if_pos h2, Finset.disjoint_left]
            intro p hpPr hpQ
            have hgt := hQgt p hpQ
            have hle := hlem r (Finset.mem_Icc.mpr ⟨hr1, by omega⟩) p hpPr
            omega
          · rw [if_neg h2]
            exact hdisj r s (Finset.mem_Icc.mpr ⟨hr1, by omega⟩)
              (Finset.mem_Icc.mpr ⟨hs1, by omega⟩) hrs

theorem exists_bounded_crt_residue (K : ℕ) (m c : ℕ → ℕ)
    (hpos : ∀ r ∈ Finset.Icc 1 K, 0 < m r)
    (hcop : ∀ r s, r ∈ Finset.Icc 1 K → s ∈ Finset.Icc 1 K → r ≠ s →
      Nat.Coprime (m r) (m s)) :
    ∃ x : ℕ, x < ∏ r ∈ Finset.Icc 1 K, m r ∧
      ∀ r ∈ Finset.Icc 1 K, x ≡ c r [MOD m r] := by
  induction K with
  | zero =>
      refine ⟨0, ?_, ?_⟩
      · rw [Finset.Icc_eq_empty (by omega : ¬ (1 : ℕ) ≤ 0), Finset.prod_empty]
        omega
      · intro r hr
        exact absurd (Finset.mem_Icc.mp hr) (by omega)
  | succ K ih =>
      have hsub : ∀ r, r ∈ Finset.Icc 1 K → r ∈ Finset.Icc 1 (K + 1) := by
        intro r hr
        rcases Finset.mem_Icc.mp hr with ⟨h1, h2⟩
        exact Finset.mem_Icc.mpr ⟨h1, by omega⟩
      obtain ⟨x₀, hx₀lt, hx₀cong⟩ := ih (fun r hr => hpos r (hsub r hr))
        (fun r s hr hs hrs => hcop r s (hsub r hr) (hsub s hs) hrs)
      have hK1mem : K + 1 ∈ Finset.Icc 1 (K + 1) :=
        Finset.mem_Icc.mpr ⟨by omega, le_refl _⟩
      have hcopA : Nat.Coprime (∏ r ∈ Finset.Icc 1 K, m r) (m (K + 1)) :=
        Nat.Coprime.prod_left fun r hr =>
          hcop r (K + 1) (hsub r hr) hK1mem
            (by rcases Finset.mem_Icc.mp hr with ⟨_, h2⟩; omega)
      have hA0 : (∏ r ∈ Finset.Icc 1 K, m r) ≠ 0 := by
        have h1 : 0 < ∏ r ∈ Finset.Icc 1 K, m r :=
          Finset.prod_pos fun r hr => hpos r (hsub r hr)
        omega
      have hm0 : m (K + 1) ≠ 0 := by
        have := hpos (K + 1) hK1mem
        omega
      have hlt := Nat.chineseRemainder_lt_mul hcopA x₀ (c (K + 1)) hA0 hm0
      obtain ⟨hcong1, hcong2⟩ := (Nat.chineseRemainder hcopA x₀ (c (K + 1))).2
      refine ⟨(Nat.chineseRemainder hcopA x₀ (c (K + 1)) : ℕ), ?_, ?_⟩
      · rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ K + 1)]
        exact hlt
      · intro r hr
        rcases Finset.mem_Icc.mp hr with ⟨hr1, hr2⟩
        by_cases hrK : r ≤ K
        · have hrmem : r ∈ Finset.Icc 1 K := Finset.mem_Icc.mpr ⟨hr1, hrK⟩
          have hdvd : m r ∣ ∏ j ∈ Finset.Icc 1 K, m j :=
            Finset.dvd_prod_of_mem m hrmem
          exact (Nat.ModEq.of_dvd hdvd hcong1).trans (hx₀cong r hrmem)
        · have hreq : r = K + 1 := by omega
          rw [hreq]
          exact hcong2

theorem exists_bounded_first_block_frame
    (b L K : ℕ) (hb : 2 ≤ b) (hK : 1 ≤ K) (hKL : K ≤ L) :
    ∃ x A : ℕ, 0 < A ∧ x < A ∧ L + 1 ≤ A ∧
      A ≤ (2 ^ (K * (K + 1)) * (L + 1)) ^ (b * K ^ 2) ∧
      (∀ p : ℕ, Nat.Prime p → p ∣ A → L < p ∧ ∃ r ∈ Finset.Icc 1 K, p ∣ x + r) ∧
      (∀ y : ℕ, ∀ r ∈ Finset.Icc 1 K, b ^ r ∣ (x + y * A + r).divisors.card) := by
  classical
  obtain ⟨P, M, hLM, hMB, hcards, hprimes, hgtL, hleM, hdisj⟩ :=
    exists_bounded_disjoint_prime_blocks L K
  set π : ℕ → ℕ := fun r => ∏ p ∈ P r, p with hπdef
  set mm : ℕ → ℕ := fun r => (π r) ^ b with hmmdef
  have hπpos : ∀ r ∈ Finset.Icc 1 K, 0 < π r := fun r hr =>
    Finset.prod_pos fun p hp => (hprimes r hr p hp).pos
  have hπ2 : ∀ r ∈ Finset.Icc 1 K, 2 ≤ π r := by
    intro r hr
    rcases Finset.mem_Icc.mp hr with ⟨hr1, hr2⟩
    have hne : (P r).Nonempty := by
      rw [← Finset.card_pos, hcards r hr]
      omega
    obtain ⟨p₀, hp₀⟩ := hne
    have h1 : p₀ ≤ π r := Nat.le_of_dvd (hπpos r hr) (Finset.dvd_prod_of_mem _ hp₀)
    have h2 := (hprimes r hr p₀ hp₀).two_le
    omega
  have hπgtL : ∀ r ∈ Finset.Icc 1 K, L < π r := by
    intro r hr
    rcases Finset.mem_Icc.mp hr with ⟨hr1, hr2⟩
    have hne : (P r).Nonempty := by
      rw [← Finset.card_pos, hcards r hr]
      omega
    obtain ⟨p₀, hp₀⟩ := hne
    have h1 : p₀ ≤ π r := Nat.le_of_dvd (hπpos r hr) (Finset.dvd_prod_of_mem _ hp₀)
    have h2 := hgtL r hr p₀ hp₀
    omega
  have hmmpos : ∀ r ∈ Finset.Icc 1 K, 0 < mm r := fun r hr => pow_pos (hπpos r hr) b
  have hmmcop : ∀ r s, r ∈ Finset.Icc 1 K → s ∈ Finset.Icc 1 K → r ≠ s →
      Nat.Coprime (mm r) (mm s) := by
    intro r s hr hs hrs
    have hππ : Nat.Coprime (π r) (π s) := by
      apply Nat.Coprime.prod_left
      intro p hp
      have h1 : Nat.Coprime (π s) p := by
        apply Nat.Coprime.prod_left
        intro p' hp'
        have hne' : p' ≠ p := by
          intro heq
          have hp'' : p ∈ P s := heq ▸ hp'
          exact (Finset.disjoint_left.mp (hdisj r s hr hs hrs) hp) hp''
        exact (Nat.coprime_primes (hprimes s hs p' hp') (hprimes r hr p hp)).mpr hne'
      exact h1.symm
    exact Nat.Coprime.pow b b hππ
  have hrle : ∀ r ∈ Finset.Icc 1 K, r ≤ (π r) ^ (b - 1) := by
    intro r hr
    rcases Finset.mem_Icc.mp hr with ⟨hr1, hr2⟩
    have h1 : π r ≤ (π r) ^ (b - 1) := Nat.le_self_pow (by omega) _
    have h2 := hπgtL r hr
    omega
  obtain ⟨x, hxlt, hxcong⟩ := exists_bounded_crt_residue K mm
    (fun r => (π r) ^ (b - 1) - r) hmmpos hmmcop
  set A : ℕ := ∏ r ∈ Finset.Icc 1 K, mm r with hAdef
  have hApos : 0 < A := Finset.prod_pos hmmpos
  have hmmdvdA : ∀ r ∈ Finset.Icc 1 K, mm r ∣ A := fun r hr =>
    Finset.dvd_prod_of_mem mm hr
  have h1mem : (1 : ℕ) ∈ Finset.Icc 1 K := Finset.mem_Icc.mpr ⟨le_refl _, hK⟩
  have hLA : L + 1 ≤ A := by
    have h1 : mm 1 ≤ A := Nat.le_of_dvd hApos (hmmdvdA 1 h1mem)
    have h2 : π 1 ≤ mm 1 := Nat.le_self_pow (by omega) _
    have h3 := hπgtL 1 h1mem
    omega
  have hshift : ∀ r ∈ Finset.Icc 1 K, x + r ≡ (π r) ^ (b - 1) [MOD mm r] := by
    intro r hr
    have h1 := (hxcong r hr).add_right r
    have h2 : (π r) ^ (b - 1) - r + r = (π r) ^ (b - 1) :=
      Nat.sub_add_cancel (hrle r hr)
    rwa [h2] at h1
  have hprogcong : ∀ y : ℕ, ∀ r ∈ Finset.Icc 1 K,
      x + y * A + r ≡ (π r) ^ (b - 1) [MOD mm r] := by
    intro y r hr
    have h1 : mm r ∣ y * A := Dvd.dvd.mul_left (hmmdvdA r hr) y
    have h2 : x + y * A + r ≡ x + 0 + r [MOD mm r] :=
      ((Nat.ModEq.refl x).add ((Nat.modEq_zero_iff_dvd).mpr h1)).add_right r
    have h3 : x + 0 + r = x + r := by ring
    rw [h3] at h2
    exact h2.trans (hshift r hr)
  have hval : ∀ y : ℕ, ∀ r ∈ Finset.Icc 1 K, ∀ p ∈ P r,
      (x + y * A + r).factorization p = b - 1 := by
    intro y r hr p hp
    exact factorization_eq_of_modEq_prod_pow b hb (P r)
      (fun p' hp' => hprimes r hr p' hp') (hπ2 r hr) _ (hprogcong y r hr) p hp
  refine ⟨x, A, hApos, hxlt, hLA, ?_, ?_, ?_⟩
  · -- modulus bound
    have hMpos : 0 < M := by omega
    have hπleMK : ∀ r ∈ Finset.Icc 1 K, π r ≤ M ^ K := by
      intro r hr
      have h1 : π r ≤ M ^ (P r).card :=
        Finset.prod_le_pow_card (P r) _ M (fun p hp => hleM r hr p hp)
      have h2 : M ^ (P r).card = M ^ r := by rw [hcards r hr]
      have h3 : M ^ r ≤ M ^ K :=
        Nat.pow_le_pow_right hMpos (Finset.mem_Icc.mp hr).2
      omega
    have hmmle : ∀ r ∈ Finset.Icc 1 K, mm r ≤ (M ^ K) ^ b := fun r hr =>
      Nat.pow_le_pow_left (hπleMK r hr) b
    have hAle1 : A ≤ ((M ^ K) ^ b) ^ K := by
      have h1 : A ≤ ((M ^ K) ^ b) ^ (Finset.Icc 1 K).card :=
        Finset.prod_le_pow_card _ _ _ hmmle
      have h2 : (Finset.Icc 1 K).card = K := by rw [Nat.card_Icc]; omega
      rwa [h2] at h1
    have hAle2 : ((M ^ K) ^ b) ^ K = M ^ (b * K ^ 2) := by
      rw [← pow_mul, ← pow_mul]
      congr 1
      ring
    have hMle : M ^ (b * K ^ 2) ≤ (2 ^ (K * (K + 1)) * (L + 1)) ^ (b * K ^ 2) :=
      Nat.pow_le_pow_left hMB _
    omega
  · -- modulus support
    intro p hp hpA
    rw [hAdef] at hpA
    obtain ⟨r, hrmem, hpmm⟩ := Prime.exists_mem_finset_dvd hp.prime hpA
    have hpπ : p ∣ π r := hp.dvd_of_dvd_pow hpmm
    obtain ⟨p', hp'mem, hpp'⟩ := Prime.exists_mem_finset_dvd hp.prime hpπ
    have heq : p = p' :=
      (Nat.prime_dvd_prime_iff_eq hp (hprimes r hrmem p' hp'mem)).mp hpp'
    have hpP : p ∈ P r := heq ▸ hp'mem
    refine ⟨hgtL r hrmem p hpP, r, hrmem, ?_⟩
    have h1 : p ∣ mm r := hpπ.trans (dvd_pow_self (π r) (by omega : b ≠ 0))
    have h2 : x + r ≡ (π r) ^ (b - 1) [MOD p] :=
      Nat.ModEq.of_dvd h1 (hshift r hrmem)
    have h3 : p ∣ (π r) ^ (b - 1) :=
      hpπ.trans (dvd_pow_self (π r) (by omega : b - 1 ≠ 0))
    have h4 : (π r) ^ (b - 1) ≡ 0 [MOD p] := (Nat.modEq_zero_iff_dvd).mpr h3
    exact (Nat.modEq_zero_iff_dvd).mp (h2.trans h4)
  · -- first-block divisibility
    intro y r hr
    have hne : x + y * A + r ≠ 0 := by
      have := (Finset.mem_Icc.mp hr).1
      omega
    have hdvd := bpow_dvd_card_divisors_of_exact_prime_block b (x + y * A + r)
      hb hne (P r) (fun p hp => hval y r hr p hp)
    rwa [hcards r hr] at hdvd

end Erdos249257

end

section

namespace Erdos257

/-- Splitting the exponent at its remainder modulo `d` gives an explicit
natural quotient. The identity also holds for `d = 0` under Lean's convention. -/
theorem mersenne_quotient_remainder (N d : ℕ) :
    ∃ z : ℕ, 2 ^ N - 1 = z * (2 ^ d - 1) + (2 ^ (N % d) - 1) := by
  refine ⟨2 ^ (N % d) * ∑ i ∈ Finset.range (N / d), (2 ^ d) ^ i, ?_⟩
  have hpow : (2 : ℕ) ^ (N % d) * (2 ^ d) ^ (N / d) = 2 ^ N := by
    rw [← pow_mul, ← pow_add, Nat.mod_add_div]
  have hr : 0 < (2 : ℕ) ^ (N % d) := by positivity
  have hk : 0 < ((2 : ℕ) ^ d) ^ (N / d) := by positivity
  have hle : (2 : ℕ) ^ (N % d) ≤ 2 ^ N := by
    simpa only [Nat.mul_one, hpow] using Nat.mul_le_mul_left (2 ^ (N % d)) (Nat.succ_le_of_lt hk)
  rw [Nat.mul_assoc, geom_sum_mul_of_one_le (Nat.succ_le_of_lt (by positivity : 0 < (2 : ℕ) ^ d)), Nat.mul_sub, hpow, Nat.mul_one]
  omega


end Erdos257

end

section

set_option autoImplicit false

namespace Erdos257Readiness

/-- With 2^k dividing N, a residue of N modulo a power of two is zero or
at least 2^k short of the upper endpoint. -/
theorem dyadicResidueGap (k j N : ℕ) (hN : 2 ^ k ∣ N) :
    N % 2 ^ j = 0 ∨ N % 2 ^ j + 2 ^ k ≤ 2 ^ j := by
  by_cases hj : j ≤ k
  · exact Or.inl (Nat.mod_eq_zero_of_dvd ((pow_dvd_pow 2 hj).trans hN))
  · right
    have hd : 2 ^ k ∣ (2 : ℕ) ^ j := pow_dvd_pow 2 (by omega)
    have hr : 2 ^ k ∣ N % 2 ^ j := (Nat.dvd_mod_iff hd).2 hN
    have hm := Nat.mod_lt N (by positivity : 0 < (2 : ℕ) ^ j)
    have hs := Nat.le_of_dvd (Nat.sub_pos_of_lt hm) (Nat.dvd_sub hd hr)
    omega

/-- A gap of m in the exponent bounds the normalized Mersenne remainder by 2⁻ᵐ. -/
theorem mersenneResidueRatio (r d m : ℕ) (hd : 0 < d) (h : r + m ≤ d) :
    ((2 : ℝ) ^ r - 1) / (2 ^ d - 1) ≤ 1 / 2 ^ m := by
  have hpow : (2 : ℝ) ^ (r + m) ≤ 2 ^ d := pow_le_pow_right₀ (by norm_num) h
  have hm : 1 ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
  have hden : 0 < (2 : ℝ) ^ d - 1 := sub_pos.mpr (one_lt_pow₀ (by norm_num) (by omega))
  rw [div_le_div_iff₀ hden (by positivity)]
  rw [pow_add] at hpow
  linarith


end Erdos257Readiness

end

section

set_option autoImplicit false

namespace Erdos257Readiness

/-- For any selection of natural-number indices, a uniform bound on the first
L remainders and geometric decay thereafter imply summability and an explicit
bound independent of the selection. The cutoff L belongs to the tail. -/
theorem uniform_remainder_tsum (D : Set ℕ) (f : ℕ → ℝ) (L : ℕ)
    {ε η : ℝ} (hε : 0 ≤ ε) (hη : 0 ≤ η)
    (hne : ∀ n ∈ D, 0 ≤ f n)
    (hhead : ∀ n ∈ D, n < L → f n ≤ ε)
    (htail : ∀ n : ℕ, n + L ∈ D → f (n + L) ≤ η * (1 / 2 : ℝ) ^ n) :
    Summable (fun n : D => f n.val) ∧
      (∑' n : D, f n.val) ≤ (L : ℝ) * ε + 2 * η := by
  classical
  have hgeom := hasSum_geometric_two.mul_left η
  have htail_le (n : ℕ) : D.indicator f (n + L) ≤ η * (1 / 2 : ℝ) ^ n := by
    by_cases hn : n + L ∈ D
    · rw [Set.indicator_of_mem hn]
      exact htail n hn
    · rw [Set.indicator_of_notMem hn]
      positivity
  have hsumTail : Summable (fun n => D.indicator f (n + L)) :=
    hgeom.summable.of_nonneg_of_le (fun n => Set.indicator_nonneg hne (n + L)) htail_le
  have hsum : Summable (D.indicator f) := (summable_nat_add_iff L).1 hsumTail
  refine ⟨summable_subtype_iff_indicator.2 hsum, ?_⟩
  rw [tsum_subtype, ← hsum.sum_add_tsum_nat_add L]
  apply add_le_add
  · calc
      ∑ n ∈ Finset.range L, D.indicator f n ≤ ∑ _n ∈ Finset.range L, ε := by
        apply Finset.sum_le_sum
        intro n hn
        by_cases hD : n ∈ D
        · rw [Set.indicator_of_mem hD]
          exact hhead n hD (Finset.mem_range.1 hn)
        · rwa [Set.indicator_of_notMem hD]
      _ = (L : ℝ) * ε := by simp
  · calc
      ∑' n : ℕ, D.indicator f (n + L) ≤ ∑' n : ℕ, η * (1 / 2 : ℝ) ^ n :=
        hsumTail.tsum_le_tsum htail_le hgeom.summable
      _ = 2 * η := hgeom.tsum_eq.trans (mul_comm _ _)


/-- If the dyadic cutoff exponent is at least 2N, the normalized Mersenne
quotient beyond that cutoff supplies the geometric envelope automatically. -/
theorem uniform_dyadic_remainder_tsum (D : Set ℕ) (f : ℕ → ℝ) (L N : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε) (hL : 2 * N ≤ 2 ^ L)
    (hne : ∀ j ∈ D, 0 ≤ f j)
    (hhead : ∀ j ∈ D, j < L → f j ≤ ε)
    (hraw : ∀ j ∈ D, L ≤ j → f j ≤ ((2 : ℝ) ^ N - 1) / (2 ^ (2 ^ j : ℕ) - 1)) :
    Summable (fun j : D => f j.val) ∧
      (∑' j : D, f j.val) ≤ (L : ℝ) * ε + 2 * (1 / (2 : ℝ) ^ N) := by
  apply uniform_remainder_tsum D f L hε (by positivity) hne hhead
  intro n hn
  have hgrowth : (2 : ℕ) ^ L + n ≤ 2 ^ (n + L) := by
    clear hn
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.succ_add, pow_succ]
      have hpos : 0 < (2 : ℕ) ^ (n + L) := by positivity
      omega
  apply (hraw (n + L) hn (by omega)).trans
  calc
    ((2 : ℝ) ^ N - 1) / (2 ^ (2 ^ (n + L) : ℕ) - 1)
        ≤ 1 / 2 ^ (N + n) := mersenneResidueRatio N _ _ (by positivity) (by omega)
    _ = 1 / (2 : ℝ) ^ N * (1 / 2) ^ n := by
      simp [pow_add, div_eq_mul_inv, mul_comm]


/-- The unsigned fractional remainder from dividing a shifted Mersenne term
by its denominator, written for the dyadic exponent indexed by j. -/
noncomputable def dyadicTermRemainder (N j : ℕ) : ℝ :=
  ((2 : ℝ) ^ (N % 2 ^ j) - 1) / (2 ^ (2 ^ j : ℕ) - 1)

/-- A uniform bound for the actual remainders over every finite or infinite
selection of dyadic terms. The bound uses the shift and the cutoff alone. -/
theorem tsum_dyadicTermRemainder (D : Set ℕ) (N k L : ℕ)
    (hN : 2 ^ k ∣ N) (hL : 2 * N ≤ 2 ^ L) :
    Summable (fun j : D => dyadicTermRemainder N j.val) ∧
      (∑' j : D, dyadicTermRemainder N j.val) ≤
        (L : ℝ) * (1 / (2 : ℝ) ^ (2 ^ k : ℕ)) + 2 * (1 / (2 : ℝ) ^ N) := by
  apply uniform_dyadic_remainder_tsum D (dyadicTermRemainder N) L N (by positivity) hL
  · intro j _
    exact div_nonneg (sub_nonneg.mpr (one_le_pow₀ (by norm_num)))
      (sub_nonneg.mpr (one_le_pow₀ (by norm_num)))
  · intro j _ _
    rcases dyadicResidueGap k j N hN with hz | hgap
    · simp [dyadicTermRemainder, hz]
    · exact mersenneResidueRatio _ _ _ (by positivity) hgap
  · intro j _ _
    unfold dyadicTermRemainder
    apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr (one_le_pow₀ (by norm_num)))
    exact sub_le_sub_right (pow_le_pow_right₀ (by norm_num) (Nat.mod_le _ _)) _


end Erdos257Readiness

end

section

namespace Erdos257Readiness

theorem summable_mersenne_reciprocals :
    Summable (fun n : ℕ => 1 / ((2 : ℝ) ^ n - 1)) := by
  have hgeom : Summable (fun n : ℕ => (2 : ℝ) * (1 / 2 : ℝ) ^ n) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left 2
  apply Summable.of_nonneg_of_le _ _ hgeom
  · intro n
    exact div_nonneg zero_le_one (sub_nonneg.mpr (one_le_pow₀ (by norm_num)))
  · intro n
    obtain rfl | hn := Nat.eq_zero_or_pos n
    · norm_num
    · have hp : (2 : ℝ) ≤ 2 ^ n := by
        simpa using pow_le_pow_right₀ (one_le_two : (1 : ℝ) ≤ 2) hn
      rw [show (2 : ℝ) * (1 / 2 : ℝ) ^ n = 2 / 2 ^ n by rw [div_pow, one_pow]; ring]
      rw [div_le_div_iff₀ (by linarith) (by positivity)]
      linarith

private theorem tsum_positive_subtype (P : ℕ → Prop) (f : ℕ → ℝ) :
    (∑' n : {n : {n : ℕ // 0 < n} // P n.val}, f n.val.val) =
      ∑' n : {n : ℕ // 0 < n ∧ P n}, f n.val := by
  let e : {n : {n : ℕ // 0 < n} // P n.val} ≃ {n : ℕ // 0 < n ∧ P n} :=
    ⟨fun n => ⟨n.val.val, n.val.property, n.property⟩,
     fun n => ⟨⟨n.val, n.property.1⟩, n.property.2⟩, fun _ => rfl, fun _ => rfl⟩
  exact e.tsum_eq (fun n => f n.val)

theorem mersenne_split (D : Set ℕ) :
    (∑' n : {n : ℕ // 0 < n ∧ n ∉ D}, 1 / ((2 : ℝ) ^ n.val - 1)) +
    (∑' n : {n : ℕ // 0 < n ∧ n ∈ D}, 1 / ((2 : ℝ) ^ n.val - 1)) =
      ∑' n : {n : ℕ // 0 < n}, 1 / ((2 : ℝ) ^ n.val - 1) := by
  let f : ℕ → ℝ := fun n => 1 / ((2 : ℝ) ^ n - 1)
  have h : Summable (fun n : {n : ℕ // 0 < n} => f n.val) :=
    summable_mersenne_reciprocals.subtype (fun n => 0 < n)
  have hs := h.tsum_subtype_add_tsum_subtype_compl
    {n : {n : ℕ // 0 < n} | n.val ∈ D}
  rw [add_comm]
  exact (congrArg₂ (· + ·) (tsum_positive_subtype (· ∈ D) f).symm
    (tsum_positive_subtype (· ∉ D) f).symm).trans hs

theorem mersenne_dyadic_split (D : Set ℕ)
    (hD : D ⊆ Set.range (fun j : ℕ => (2 : ℕ) ^ j)) :
    (∑' n : {n : ℕ // 0 < n ∧ n ∉ D}, 1 / ((2 : ℝ) ^ n.val - 1)) +
    (∑' j : {j : ℕ // (2 : ℕ) ^ j ∈ D}, 1 / ((2 : ℝ) ^ ((2 : ℕ) ^ j.val) - 1)) =
      ∑' n : {n : ℕ // 0 < n}, 1 / ((2 : ℝ) ^ n.val - 1) := by
  let g (j : {j : ℕ // (2 : ℕ) ^ j ∈ D}) : {n : ℕ // 0 < n ∧ n ∈ D} :=
    ⟨2 ^ j.val, pow_pos (by decide) _, j.property⟩
  have hg : Function.Bijective g := by
    constructor
    · intro x y h
      exact Subtype.ext (Nat.pow_right_injective (by decide : 2 ≤ 2) (congrArg Subtype.val h))
    · intro n
      obtain ⟨j, hj⟩ := hD n.property.2
      change 2 ^ j = n.val at hj
      exact ⟨⟨j, hj.symm ▸ n.property.2⟩, Subtype.ext hj⟩
  have hsum := (Equiv.ofBijective g hg).tsum_eq
    (fun n => 1 / ((2 : ℝ) ^ n.val - 1))
  exact (congrArg (_ + ·) hsum).trans (mersenne_split D)


end Erdos257Readiness

end

section

set_option autoImplicit false

open Filter Topology

namespace Erdos257Readiness

/-- Integer shifts that take E to the integer lattice and W back to its own
class modulo integers transfer irrationality from E to E − W. The two limits
give signed approximation errors for explicit integer witnesses. -/
theorem irrational_sub_of_integer_returns
    {E W : ℝ} (hE : Irrational E)
    (shift baseInteger returnInteger : ℕ → ℤ)
    (hbase : Tendsto (fun n => (shift n : ℝ) * E - baseInteger n) atTop (𝓝 0))
    (hreturn : Tendsto (fun n => ((shift n : ℝ) - 1) * W - returnInteger n)
      atTop (𝓝 0)) :
    Irrational (E - W) := by
  apply (irrational_iff_ne_rational _).2
  intro p q hq hrat
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have hp : (E - W) * (q : ℝ) = p := (eq_div_iff hq0).1 hrat
  have limit : Tendsto
      (fun n => (q : ℝ) * W - (q : ℝ) *
        (((shift n : ℝ) * E - baseInteger n) -
         (((shift n : ℝ) - 1) * W - returnInteger n)))
      atTop (𝓝 ((q : ℝ) * W)) := by
    simpa using
      (tendsto_const_nhds (x := (q : ℝ) * W)).sub ((hbase.sub hreturn).const_mul (q : ℝ))
  have member : (q : ℝ) * W ∈ Set.range ((↑) : ℤ → ℝ) := by
    apply Real.isClosed_range_intCast.mem_of_tendsto limit
    apply Eventually.of_forall
    intro n
    refine ⟨q * (baseInteger n - returnInteger n) - shift n * p, ?_⟩
    push_cast
    linear_combination (shift n : ℝ) * hp
  obtain ⟨z, hz⟩ := member
  apply hE.ne_rational (p + z) q
  apply (eq_div_iff hq0).2
  push_cast
  nlinarith only [hp, hz]


end Erdos257Readiness

end

section

set_option autoImplicit false

namespace Erdos257Readiness

/-- The restricted Erdős 257 assertion. Exponents in the sum are positive natural
numbers, and D may contain any selection of the powers 1, 2, 4, 8, ... . -/
def DyadicDeletionIrrationality : Prop :=
  ∀ D : Set ℕ, D ⊆ Set.range (fun j : ℕ => (2 : ℕ) ^ j) →
    Irrational (∑' n : {n : ℕ // 0 < n ∧ n ∉ D}, 1 / ((2 : ℝ) ^ n.val - 1))


end Erdos257Readiness

end

section

set_option autoImplicit false

open Filter Topology

namespace Erdos257Readiness

/-- The deleted terms indexed by their dyadic exponent indices. -/
noncomputable def dyadicDeletedSum (J : Set ℕ) : ℝ :=
  ∑' j : J, 1 / ((2 : ℝ) ^ ((2 : ℕ) ^ j.val) - 1)

private theorem integer_tsum_of_integer_terms {ι : Type*} {f : ι → ℝ}
    (hs : Summable f) (hz : ∀ i, ∃ z : ℤ, (z : ℝ) = f i) :
    ∃ z : ℤ, (z : ℝ) = ∑' i, f i := by
  apply Real.isClosed_range_intCast.mem_of_tendsto hs.hasSum
  apply Eventually.of_forall
  intro s
  choose z h using hz
  exact ⟨∑ i ∈ s, z i, by simp [h]⟩

private theorem dyadic_term_integer_part (N j : ℕ) :
    ∃ z : ℤ, (z : ℝ) =
        ((2 : ℝ) ^ N - 1) * (1 / ((2 : ℝ) ^ ((2 : ℕ) ^ j) - 1)) -
        dyadicTermRemainder N j := by
  let d := (2 : ℕ) ^ j
  let r := N % d
  obtain ⟨z, hz⟩ := Erdos257.mersenne_quotient_remainder N d
  have hr : 1 ≤ (2 : ℕ) ^ r := Nat.succ_le_of_lt (by positivity)
  have hd : 1 ≤ (2 : ℕ) ^ d := Nat.succ_le_of_lt (by positivity)
  have hn : 1 ≤ (2 : ℕ) ^ N := Nat.succ_le_of_lt (by positivity)
  change (2 : ℕ) ^ N - 1 = z * (2 ^ d - 1) + (2 ^ r - 1) at hz
  have hreal : (2 : ℝ) ^ N - 1 = z * ((2 : ℝ) ^ d - 1) + ((2 : ℝ) ^ r - 1) := by
    exact_mod_cast hz
  have hpos : 0 < d := by dsimp [d]; positivity
  have hden : (2 : ℝ) ^ d - 1 ≠ 0 :=
    ne_of_gt (sub_pos.mpr (one_lt_pow₀ (by norm_num) (by omega)))
  refine ⟨z, ?_⟩
  change (((z : ℤ) : ℝ)) = ((2 : ℝ) ^ N - 1) * (1 / (2 ^ d - 1)) -
    (2 ^ r - 1) / (2 ^ d - 1)
  push_cast
  rw [hreal]
  field_simp
  ring

/-- The entire shifted deleted sum differs from an integer by precisely the
sum of the unsigned Euclidean remainders, for every set of dyadic indices. -/
theorem deleted_shift_exact (J : Set ℕ) (N : ℕ) :
    ∃ z : ℤ, ((2 : ℝ) ^ N - 1) * dyadicDeletedSum J - z =
      ∑' j : J, dyadicTermRemainder N j.val := by
  let f (j : J) := 1 / ((2 : ℝ) ^ ((2 : ℕ) ^ j.val) - 1)
  have hsub : Summable f :=
    (summable_mersenne_reciprocals.comp_injective
      (Nat.pow_right_injective (by decide : 2 ≤ 2))).subtype (· ∈ J)
  have hmul := hsub.mul_left ((2 : ℝ) ^ N - 1)
  have hcut : 2 * N ≤ 2 ^ (N + 1) := by
    rw [pow_succ, mul_comm]
    exact Nat.mul_le_mul_right 2 (Nat.lt_two_pow_self.le)
  have hrem := (tsum_dyadicTermRemainder J N 0 (N+1) (by simp) hcut).1
  obtain ⟨z, hz⟩ := integer_tsum_of_integer_terms (hmul.sub hrem)
    (fun j => dyadic_term_integer_part N j.val)
  refine ⟨z, ?_⟩
  rw [hmul.tsum_sub hrem, hsub.tsum_mul_left] at hz
  change ((2 : ℝ) ^ N - 1) * (∑' j, f j) - z = _
  linarith only [hz]

/-- The selected shifts return any fixed dyadic deletion sum to its own class
modulo integers when the dyadic-divisibility and cutoff errors tend to zero. -/
theorem deleted_sum_integer_returns (J : Set ℕ) (N L : ℕ → ℕ)
    (hdiv : ∀ᶠ k in atTop, 2 ^ k ∣ N k)
    (hcut : ∀ᶠ k in atTop, 2 * N k ≤ 2 ^ L k)
    (hN : Tendsto N atTop atTop)
    (hL : Tendsto (fun k => (L k : ℝ) * (1 / (2 : ℝ) ^ ((2 : ℕ) ^ k)))
      atTop (𝓝 0)) :
    ∃ Z : ℕ → ℤ, Tendsto (fun k => ((2 : ℝ) ^ N k - 1) * dyadicDeletedSum J - Z k)
      atTop (𝓝 0) := by
  choose Z hZ using fun k => deleted_shift_exact J (N k)
  refine ⟨Z, ?_⟩
  have hgeo : Tendsto (fun k => 1 / (2 : ℝ) ^ N k) atTop (𝓝 0) := by
    simpa [Function.comp_def, div_pow] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).comp hN
  apply squeeze_zero'
    (Eventually.of_forall fun k => (hZ k).symm ▸ tsum_nonneg fun j =>
      div_nonneg (sub_nonneg.mpr (one_le_pow₀ (by norm_num)))
        (sub_nonneg.mpr (one_le_pow₀ (by norm_num))))
    _ (by simpa using hL.add (hgeo.const_mul 2))
  filter_upwards [hdiv, hcut] with k hd hc
  rw [hZ k]
  simpa using (tsum_dyadicTermRemainder J (N k) k (L k) hd hc).2


end Erdos257Readiness

end

section

set_option autoImplicit false

open Filter Topology

namespace Erdos257Readiness

/-- The full sum on positive exponents. -/
noncomputable def fullMersenneSum : ℝ :=
  ∑' a : {n : ℕ // 0 < n}, 1 / ((2 : ℝ) ^ a.val - 1)

/-- Nonzero signed errors tending to zero exclude every rational denominator. -/
theorem irrational_of_nonzero_integer_shifts {E : ℝ} (A Z : ℕ → ℤ)
    (hne : ∀ᶠ n in atTop, (A n : ℝ) * E - Z n ≠ 0)
    (hlim : Tendsto (fun n => (A n : ℝ) * E - Z n) atTop (𝓝 0)) :
    Irrational E := by
  apply (irrational_iff_ne_rational _).2
  intro p q hq hrat
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have hp : E * (q : ℝ) = p := (eq_div_iff hq0).1 hrat
  have hscaled : Tendsto (fun n => |(q : ℝ) * ((A n : ℝ) * E - Z n)|) atTop (𝓝 0) := by
    simpa using (hlim.const_mul (q : ℝ)).abs
  obtain ⟨n, hn, hb⟩ := (hne.and (hscaled.eventually_lt_const (by norm_num : (0 : ℝ) < 1))).exists
  have hi : ((A n * p - q * Z n : ℤ) : ℝ) = (q : ℝ) * ((A n : ℝ) * E - Z n) := by
    push_cast
    linear_combination - (A n : ℝ) * hp
  rw [← hi] at hb
  have hcast : |A n * p - q * Z n| < (1 : ℤ) := by exact_mod_cast hb
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hcast
  have hz : A n * p - q * Z n = 0 := by omega
  exact (mul_ne_zero hq0 hn) (by rw [← hi, hz, Int.cast_zero])

private theorem sq_le_two_pow_of_four_le (k : ℕ) (h : 4 ≤ k) : k*k ≤ 2 ^ k := by
  induction k, h using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    rw [pow_succ]
    calc
      (k + 1) * (k + 1) ≤ (k*k)*2 := by nlinarith [Nat.mul_self_le_mul_self hk]
      _ ≤ 2 ^ k * 2 := Nat.mul_le_mul_right 2 ih

/-- A cutoff growing at most exponentially in k still gives zero error after
multiplication by the uniform bound 2^(-2^k) for each head remainder. -/
theorem tendsto_cutoff_of_exponential_bound (L : ℕ → ℕ) (C : ℕ)
    (hL : ∀ᶠ k in atTop, L k ≤ 2 ^ (C * (k+1))) :
    Tendsto (fun k => (L k : ℝ) * (1 / (2 : ℝ) ^ ((2 : ℕ) ^ k)))
      atTop (𝓝 0) := by
  have hgeo : Tendsto (fun k : ℕ => 1 / (2 : ℝ) ^ k) atTop (𝓝 0) := by
    simpa [div_pow] using
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)
  apply squeeze_zero' (Eventually.of_forall fun k => by positivity) _ hgeo
  filter_upwards [hL, eventually_ge_atTop (C+4)] with k hcap hk
  have hg : C * (k+1) + k ≤ (2 : ℕ) ^ k := by
    apply le_trans _ (sq_le_two_pow_of_four_le k (by omega))
    nlinarith [Nat.mul_le_mul_right (k + 1) hk]
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  calc
    (L k : ℝ) * 2 ^ k ≤ (2 : ℝ) ^ (C * (k+1)) * 2 ^ k := by
      gcongr
      exact_mod_cast hcap
    _ = 2 ^ (C * (k+1) + k) := (pow_add ..).symm
    _ ≤ 2 ^ (2 ^ k : ℕ) := pow_le_pow_right₀ (by norm_num) hg

/-- Polynomial logarithmic height is a convenient sufficient condition for a
cutoff with vanishing total head error. -/
theorem cutoffs_of_polynomial_log_height (N : ℕ → ℕ) (C d : ℕ)
    (hsize : ∀ᶠ k in atTop, N k ≤ 2 ^ (C * (k+1) ^ d)) :
    ∃ L : ℕ → ℕ, (∀ᶠ k in atTop, 2 * N k ≤ 2 ^ L k) ∧
      Tendsto (fun k => (L k : ℝ) * (1 / (2 : ℝ) ^ ((2 : ℕ) ^ k))) atTop (𝓝 0) := by
  let L (k : ℕ) := C * (k+1)^d + 1
  refine ⟨L, ?_, tendsto_cutoff_of_exponential_bound L (C+d+1) ?_⟩
  · filter_upwards [hsize] with k hk
    simpa [L, pow_succ, Nat.mul_comm] using Nat.mul_le_mul_left 2 hk
  · apply Eventually.of_forall
    intro k
    have hp : (k+1)^d ≤ (2^k)^d := Nat.pow_le_pow_left (Nat.lt_two_pow_self : k < 2^k) d
    have hc : C ≤ 2^C := Nat.lt_two_pow_self.le
    have hc1 : C * (k+1)^d ≤ 2^(C+k*d) := by
      simpa [pow_add, pow_mul] using Nat.mul_le_mul hc hp
    have hpos : 0 < (2:ℕ)^(C+k*d) := by positivity
    calc
      L k ≤ 2^(C+k*d+1) := by dsimp [L]; rw [pow_succ]; omega
      _ ≤ 2^((C+d+1)*(k+1)) := Nat.pow_le_pow_right (by decide) (by nlinarith)

theorem dyadicDeletion_of_shifts_of_irrational (N L : ℕ → ℕ) (Z : ℕ → ℤ)
    (hdiv : ∀ᶠ k in atTop, 2 ^ k ∣ N k)
    (hcut : ∀ᶠ k in atTop, 2 * N k ≤ 2 ^ L k)
    (hN : Tendsto N atTop atTop)
    (hL : Tendsto (fun k => (L k : ℝ) * (1 / (2 : ℝ) ^ ((2 : ℕ) ^ k)))
      atTop (𝓝 0))
    (hE : Irrational fullMersenneSum)
    (hbase : Tendsto (fun k => (2 : ℝ) ^ N k * fullMersenneSum - Z k) atTop (𝓝 0)) :
    DyadicDeletionIrrationality := by
  intro D hD
  let J : Set ℕ := {j | (2 : ℕ) ^ j ∈ D}
  obtain ⟨V, hV⟩ := deleted_sum_integer_returns J N L hdiv hcut hN hL
  have hret := irrational_sub_of_integer_returns hE (fun k => (2 : ℤ) ^ N k) Z V
    (by simpa using hbase) (by simpa using hV)
  have hs := mersenne_dyadic_split D hD
  change _ + dyadicDeletedSum J = fullMersenneSum at hs
  rw [eq_sub_of_add_eq hs]
  exact hret

/-- Shift data simultaneously giving a nonzero vanishing full-sum error, the
required dyadic divisibility, and a sufficiently small cutoff imply the
restricted irrationality assertion exactly as stated on positive exponents. -/
theorem dyadicDeletion_of_shifts (N L : ℕ → ℕ) (Z : ℕ → ℤ)
    (hdiv : ∀ᶠ k in atTop, 2 ^ k ∣ N k)
    (hcut : ∀ᶠ k in atTop, 2 * N k ≤ 2 ^ L k)
    (hN : Tendsto N atTop atTop)
    (hL : Tendsto (fun k => (L k : ℝ) * (1 / (2 : ℝ) ^ ((2 : ℕ) ^ k)))
      atTop (𝓝 0))
    (hnonzero : ∀ᶠ k in atTop, (2 : ℝ) ^ N k * fullMersenneSum - Z k ≠ 0)
    (hbase : Tendsto (fun k => (2 : ℝ) ^ N k * fullMersenneSum - Z k) atTop (𝓝 0)) :
    DyadicDeletionIrrationality := by
  apply dyadicDeletion_of_shifts_of_irrational N L Z hdiv hcut hN hL _ hbase
  exact irrational_of_nonzero_integer_shifts (fun k => (2 : ℤ) ^ N k) Z
    (by simpa using hnonzero) (by simpa using hbase)


end Erdos257Readiness

end

section

/-!
# Divisor-count averages on progressions with bounded common factor

For an individual divisor `d`, the period of its congruence is
`d / gcd d Q`. If the congruence has a solution, `gcd d Q` divides
`gcd Q a`. This gives a harmonic bound for the average divisor count,
and hence a simultaneous weighted bound for one shift.

The classical divisor-hyperbola averaging strategy is also used in
the public Erdős 249/257 certificate kernel. The proofs below work
directly with the possibly noncoprime progression.
-/

open Finset

namespace Erdos257Readiness

/-- Every solvable congruence occupies one residue class modulo the
reduced modulus. Dividing by that modulus injects the solutions into an
interval of the required size. -/
private theorem count_dividing_progression (a Q T d : ℕ) (hd : 0 < d) :
    ((range T).filter fun t ↦ d ∣ a + t*Q).card ≤ T / (d / d.gcd Q) + 1 := by
  classical
  let S := (range T).filter fun t ↦ d ∣ a + t*Q
  let p := d / d.gcd Q
  have hcard : S.card ≤ (range (T / p + 1)).card := by
    apply card_le_card_of_injOn (fun t ↦ t / p)
    · intro t ht
      have ht' := mem_range.mp (mem_filter.mp ht).1
      exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right ht'.le))
    · intro s hs t ht hdiv
      have hs0 : a + s*Q ≡ 0 [MOD d] := Nat.modEq_zero_iff_dvd.mpr (mem_filter.mp hs).2
      have ht0 : a + t*Q ≡ 0 [MOD d] := Nat.modEq_zero_iff_dvd.mpr (mem_filter.mp ht).2
      have hprod := Nat.ModEq.add_left_cancel' a (hs0.trans ht0.symm)
      have hrem : s % p = t % p := hprod.cancel_right_div_gcd hd
      have hsId := Nat.mod_add_div s p
      have htId := Nat.mod_add_div t p
      change s / p = t / p at hdiv
      rw [hrem, hdiv] at hsId
      exact hsId.symm.trans htId
  simpa [S, p] using hcard

/-- A positive divisor with any solution costs at most one full gcd
factor in the count. No coprimality assumption is used. -/
theorem divisor_progression_count_le {a Q T d ℓ : ℕ} (hd : 0 < d) (hQ : 0 < Q)
    (hg : Q.gcd a ≤ ℓ) :
    (((range T).filter fun t ↦ d ∣ a + t*Q).card : ℝ) ≤ T * ℓ / (d : ℝ) + 1 := by
  classical
  by_cases h : ((range T).filter fun t ↦ d ∣ a + t*Q).Nonempty
  · obtain ⟨t, ht⟩ := h
    have hgQ := Nat.gcd_dvd_right d Q
    have hga : d.gcd Q ∣ a := (Nat.dvd_add_left (dvd_mul_of_dvd_right hgQ t)).mp
      ((Nat.gcd_dvd_left d Q).trans (mem_filter.mp ht).2)
    have hgBound : d.gcd Q ≤ ℓ := (Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ hQ)
      (Nat.dvd_gcd hgQ hga)).trans hg
    have hp := Nat.div_mul_cancel (Nat.gcd_dvd_left d Q)
    have hfloor := Nat.div_mul_le_self T (d / d.gcd Q)
    have hmul : T / (d / d.gcd Q) * d ≤ T * ℓ := calc
      _ = (T / (d / d.gcd Q) * (d / d.gcd Q)) * d.gcd Q := by rw [mul_assoc, hp]
      _ ≤ T * ℓ := Nat.mul_le_mul hfloor hgBound
    have hcast : (↑(T / (d / d.gcd Q)) : ℝ) ≤ T * ℓ / (d : ℝ) := by
      apply (le_div_iff₀ (by exact_mod_cast hd)).2
      exact_mod_cast hmul
    calc _ ≤ (↑(T / (d / d.gcd Q)) : ℝ) + 1 := by
            exact_mod_cast count_dividing_progression a Q T d hd
         _ ≤ _ := by linarith
  · rw [Finset.not_nonempty_iff_eq_empty.mp h]
    simp
    positivity

/-- Pair divisors by the involution `d ↦ n/d`. At least one member
of each pair is at most `U` when `n≤U²`. -/
private theorem pair_divisors (n U : ℕ) (hn : n ≤ U^2) :
    n.divisors.card ≤ 2*((Icc 1 U).filter fun d ↦ d ∣ n).card := by
  classical
  let small := (Icc 1 U).filter fun d ↦ d ∣ n
  have hsubset : n.divisors ⊆ small ∪ small.image (fun d ↦ n/d) := by
    intro d hd
    obtain ⟨hdvd, hn0⟩ := Nat.mem_divisors.mp hd
    have hprod := Nat.div_mul_cancel hdvd
    have hdpos := Nat.pos_of_mem_divisors hd
    by_cases hdU : d ≤ U
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_Icc.mpr ⟨hdpos, hdU⟩, hdvd⟩)
    · have hpartner : 0 < n/d := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd) hdpos
      have hU : n/d ≤ U := by
        by_contra! hbad
        have hprod' := Nat.mul_le_mul hbad (show U+1 ≤ d by omega)
        nlinarith
      apply mem_union_right
      exact mem_image.mpr ⟨n/d, mem_filter.mpr ⟨mem_Icc.mpr ⟨hpartner,hU⟩,
        ⟨d,hprod.symm⟩⟩, Nat.div_div_self hdvd hn0⟩
  calc n.divisors.card ≤ _ := card_le_card hsubset
       _ ≤ small.card + (small.image fun d ↦ n/d).card := card_union_le _ _
       _ ≤ 2*small.card := by have h := card_image_le (f := fun d ↦ n/d) (s := small); omega

/-- Total divisor count over the progression. The additive `2U` pays once
per trial divisor and the leading term is harmonic in the square cutoff. -/
theorem sum_divisors_progression_le {a Q T U ℓ : ℕ} (hQ : 0 < Q)
    (hg : Q.gcd a ≤ ℓ) (hU : ∀ t < T, a+t*Q ≤ U^2) :
    ∑ t ∈ range T, ((a+t*Q).divisors.card : ℝ) ≤
      2*((T : ℝ)*ℓ*(1+Real.log U)+U) := by
  classical
  let Ds := Icc 1 U
  let count (d : ℕ) := ((range T).filter fun t ↦ d ∣ a+t*Q).card
  have htranspose :
      ∑ t ∈ range T, ((Ds.filter fun d ↦ d ∣ a+t*Q).card : ℝ) =
      ∑ d ∈ Ds, (count d : ℝ) := by
    change _ = ∑ d ∈ Ds, (((range T).filter fun t ↦ d ∣ a+t*Q).card : ℝ)
    simp_rw [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    exact Finset.sum_comm
  have hh : ∑ d ∈ Ds, (d : ℝ)⁻¹ ≤ 1 + Real.log U := by
    simpa [Ds, harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using
      harmonic_le_one_add_log U
  calc ∑ t ∈ range T, ((a+t*Q).divisors.card : ℝ)
    _ ≤ ∑ t ∈ range T, 2*((Ds.filter fun d ↦ d ∣ a+t*Q).card : ℝ) := by
      apply sum_le_sum
      intro t ht
      exact_mod_cast pair_divisors (a+t*Q) U (hU t (mem_range.mp ht))
    _ = 2 * ∑ d ∈ Ds, (count d : ℝ) := by rw [← Finset.mul_sum, htranspose]
    _ ≤ 2 * ∑ d ∈ Ds, ((T : ℝ)*ℓ/d + 1) := by
      gcongr with d hd
      exact divisor_progression_count_le (mem_Icc.mp hd).1 hQ hg
    _ = 2 * ((T : ℝ)*ℓ*(∑ d ∈ Ds, (d : ℝ)⁻¹)+U) := by
      simp [Ds, div_eq_mul_inv, sum_add_distrib, ← Finset.mul_sum]
    _ ≤ _ := by gcongr

/-- Extract one row from a bounded average with a common positive number
of samples. -/
private theorem exists_le_average_bound {T : ℕ} (hT : 0 < T) {f : ℕ → ℝ} {M : ℝ}
    (h : ∑ t ∈ range T, f t ≤ T*M) : ∃ t < T, f t ≤ M := by
  by_contra! hn
  have hstrict : (∑ _t ∈ range T, M) < ∑ t ∈ range T, f t :=
    sum_lt_sum_of_nonempty (nonempty_range_iff.mpr hT.ne') (fun t ht ↦ hn t (mem_range.mp ht))
  simpa [nsmul_eq_mul] using (not_lt_of_ge h) (by simpa using hstrict)

/-- For every sufficiently bounded CRT progression, one positive shift
controls the whole middle tail simultaneously, including offsets sharing
a nontrivial gcd with the step. -/
theorem exists_small_middle_tail {k Q r : ℕ} (hQ : 0 < Q) (hr : r < Q)
    (hJ : k^6 ≤ Q) (hg : ∀ ℓ, k < ℓ → ℓ ≤ k^6 → Q.gcd (r+ℓ) ≤ ℓ) :
    ∃ t < Q^3,
      ∑ ℓ ∈ Ioc k (k^6), (((r+(t+1)*Q+ℓ).divisors.card : ℝ) / 2^ℓ) ≤
      ∑ ℓ ∈ Ioc k (k^6), (2*(ℓ : ℝ)*(1+Real.log (2*(Q : ℝ)^2))+4)/2^ℓ := by
  classical
  let T := Q^3
  let U := 2*Q^2
  let S := Ioc k (k^6)
  have hT : 0 < T := pow_pos hQ 3
  apply exists_le_average_bound hT
  change ∑ t ∈ range T, (∑ ℓ ∈ S, (((r+(t+1)*Q+ℓ).divisors.card : ℝ) / 2^ℓ)) ≤ _
  rw [Finset.sum_comm, Finset.mul_sum]
  apply sum_le_sum
  intro ℓ hℓ
  have hℓ' := mem_Ioc.mp hℓ
  have hc : Q.gcd (r+ℓ+Q) ≤ ℓ := by simpa using hg ℓ hℓ'.1 hℓ'.2
  have hU : ∀ t < T, r+ℓ+Q+t*Q ≤ U^2 := by
    intro t ht
    have ht1 : t+1 ≤ Q^3 := ht
    have hprod := Nat.mul_le_mul_right Q ht1
    have hQ4 : Q ≤ Q^4 := Nat.le_self_pow (by decide) Q
    have hℓQ := hℓ'.2.trans hJ
    dsimp [U]
    nlinarith
  have havg := sum_divisors_progression_le hQ hc hU
  have hforms (t : ℕ) : r+ℓ+Q+t*Q = r+(t+1)*Q+ℓ := by ring
  simp_rw [hforms] at havg
  have hUt : (U : ℝ) ≤ 2*(T : ℝ) := by
    have h2 : Q^2 ≤ Q^3 := Nat.pow_le_pow_right hQ (by decide)
    dsimp [U,T]
    exact_mod_cast Nat.mul_le_mul_left 2 h2
  have hlog : (U : ℝ) = 2*(Q : ℝ)^2 := by simp [U]
  rw [← Finset.sum_div]
  have hresult : ∑ t ∈ range T, ((r+(t+1)*Q+ℓ).divisors.card : ℝ) ≤
      T*(2*(ℓ : ℝ)*(1+Real.log (2*(Q : ℝ)^2))+4) := by
    rw [← hlog]
    linarith
  convert div_le_div_of_nonneg_right hresult (by positivity : (0:ℝ) ≤ 2^ℓ) using 1
  ring


end Erdos257Readiness

end

section

set_option autoImplicit false
namespace Erdos257Readiness
open scoped BigOperators
open ArithmeticFunction

/-- The ordinary Lambert series at one half, expanded in divisor counts.
The rearrangement is Mathlib's Lambert identity at divisor weight zero. -/
theorem full_mersenne_eq_divisor_sum :
    (∑' a : {n : ℕ // 0 < n}, 1 / ((2 : ℝ) ^ a.val - 1)) =
      ∑' n : ℕ, (n.divisors.card : ℝ) / 2 ^ n := by
  have h := tsum_pow_div_one_sub_eq_tsum_sigma (r := (1/2 : ℝ)) (by norm_num) 0
  have hsum : Summable (fun n : ℕ => (n.divisors.card : ℝ) / 2 ^ n) := by
    apply Summable.of_nonneg_of_le (f := fun n : ℕ => (n : ℝ) ^ 1 * (1 / 2 : ℝ) ^ n)
    · intro n; positivity
    · intro n
      rw [pow_one, one_div_pow, div_eq_mul_one_div]
      gcongr
      exact_mod_cast Nat.card_divisors_le_self n
    · exact summable_pow_mul_geometric_of_norm_lt_one 1 (by norm_num)
  rw [← tsum_zero_pnat_eq_tsum_nat hsum]
  simp only [Nat.divisors_zero, Finset.card_empty, Nat.cast_zero, zero_div, zero_add]
  calc
    _ = ∑' n : ℕ+, (n : ℝ) ^ 0 * (1 / 2 : ℝ) ^ (n : ℕ) / (1 - (1 / 2 : ℝ) ^ (n : ℕ)) := by
      apply tsum_congr
      intro n
      simp only [pow_zero, one_mul, one_div_pow]
      have hpos : (0 : ℝ) < 2 ^ (n : ℕ) := by positivity
      change 1 / ((2 : ℝ)^n.val-1) = (1/(2:ℝ)^n.val)/(1-1/(2:ℝ)^n.val)
      have hsub : (1 : ℝ) - 1 / 2 ^ (n : ℕ) = (2 ^ (n : ℕ) - 1) / 2 ^ (n : ℕ) := by
        field_simp
      rw [hsub, div_div_div_cancel_right₀ hpos.ne']
    _ = _ := h.trans (tsum_congr (fun n => by simp [sigma_eq_sum_div, div_eq_mul_inv]))
end Erdos257Readiness

end

section

set_option autoImplicit false

open Filter Topology

namespace Erdos257Readiness

/-- The tail of the normalized divisor series after position `N+L`. -/
noncomputable def divisorWindowTail (N L : ℕ) : ℝ :=
  ∑' n : ℕ, (((N + (n + (L+1))).divisors.card : ℝ) / 2 ^ (n + (L+1)))

private theorem nat_half_hasSum :
    HasSum (fun n : ℕ => (n : ℝ) * (1/2 : ℝ)^n) 2 := by
  simpa only [show (1/2 : ℝ) / (1 - 1/2)^2 = 2 by norm_num] using
    hasSum_coe_mul_geometric_of_norm_lt_one (r := (1/2 : ℝ)) (by norm_num)

private theorem divisor_half_summable :
    Summable (fun n : ℕ => (n.divisors.card : ℝ) / (2:ℝ)^n) := by
  apply nat_half_hasSum.summable.of_nonneg_of_le (fun n => by positivity)
  intro n
  simp only [one_div, inv_pow, ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.card_divisors_le_self n) (by positivity)

private theorem shifted_half_summable (N : ℕ) :
    Summable (fun j : ℕ => ((N+j).divisors.card : ℝ) / (2:ℝ)^j) := by
  have h := ((summable_nat_add_iff N).2 divisor_half_summable).mul_left ((2:ℝ)^N)
  refine h.congr (fun j => ?_)
  rw [Nat.add_comm j N, pow_add]
  field_simp

/-- The opening divisibility window makes every term through `N+k` an integer
after multiplication by `2^N`. -/
theorem shift_divisor_series (N k : ℕ)
    (hdiv : ∀ j : ℕ, 0 < j → j ≤ k → (2:ℕ)^j ∣ (N+j).divisors.card) :
    ∃ z : ℤ, (2:ℝ)^N * (∑' n : ℕ, (n.divisors.card : ℝ) / (2:ℝ)^n) - z =
        divisorWindowTail N k := by
  classical
  have term (n : ℕ) (hn : n ≤ N+k) :
      ∃ z : ℕ, (2:ℝ)^N * ((n.divisors.card : ℝ) / 2^n) = z := by
    by_cases h : n ≤ N
    · use 2^(N-n) * n.divisors.card
      have he : (2:ℝ)^N = 2^(N-n)*2^n := by rw [← pow_add, Nat.sub_add_cancel h]
      rw [he]
      push_cast
      field_simp
    · obtain ⟨z, hz⟩ := hdiv (n-N) (by omega) (by omega)
      rw [show N+(n-N)=n by omega] at hz
      use z
      rw [hz, show (2:ℝ)^n=2^N*2^(n-N) by rw [← pow_add]; congr 1; omega]
      push_cast
      field_simp
  let z (n : ℕ) : ℕ := if hn : n ≤ N+k then (term n hn).choose else 0
  refine ⟨(∑ n ∈ Finset.range (N+k+1), z n : ℕ), ?_⟩
  rw [← divisor_half_summable.sum_add_tsum_nat_add (N+k+1), mul_add, Finset.mul_sum]
  have hsum :
      (∑ n ∈ Finset.range (N+k+1), (2:ℝ)^N * ((n.divisors.card : ℝ)/2^n)) =
      ∑ n ∈ Finset.range (N+k+1), (z n : ℝ) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hn' : n ≤ N+k := by simpa using hn
    simpa [z,hn'] using (term n hn').choose_spec
  rw [hsum]
  push_cast
  rw [add_comm (∑ n ∈ _, (z n : ℝ)), add_sub_cancel_right, ← tsum_mul_left]
  unfold divisorWindowTail
  apply tsum_congr
  intro n
  rw [show n + (N+k+1) = N + (n+(k+1)) by omega, pow_add]
  field_simp

theorem divisorWindowTail_pos (N k : ℕ) : 0 < divisorWindowTail N k := by
  apply ((summable_nat_add_iff (k+1)).2 (shifted_half_summable N)).tsum_pos (fun _ => by positivity) 0
  apply div_pos _ (by positivity)
  exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega)⟩

/-- A base-two geometric envelope for all terms after the closing position. -/
theorem divisor_tail_le (N L : ℕ) :
    divisorWindowTail N L ≤ (N+L+2 : ℝ)/2^L := by
  let C : ℝ := (N:ℝ) + L + 1
  have hnat := nat_half_hasSum
  have hs := (((hasSum_geometric_two.mul_left C).add hnat).div_const ((2:ℝ)^(L+1)))
  have hle (n : ℕ) :
      (((N+(n+(L+1))).divisors.card : ℝ)/2^(n+(L+1))) ≤
        (C * (1/2:ℝ)^n + n * (1/2:ℝ)^n) / 2^(L+1) := by
    calc
      _ ≤ ((N+(n+(L+1)) : ℕ):ℝ) / 2^(n+(L+1)) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact_mod_cast Nat.card_divisors_le_self _
      _ = _ := by
        dsimp [C]
        push_cast
        rw [pow_add]
        simp only [one_div, inv_pow]
        ring
  have htail := ((summable_nat_add_iff (L+1)).2 (shifted_half_summable N))
  calc
    divisorWindowTail N L ≤ _ := htail.tsum_le_tsum hle hs.summable
    _ = (C*2+2) / 2^(L+1) := hs.tsum_eq
    _ = _ := by rw [pow_succ]; dsimp [C]; ring

/-- Split the normalized tail into its middle interval and its far tail. -/
theorem divisor_tail_middle (N k L : ℕ) (hkL : k ≤ L) :
    divisorWindowTail N k =
      (∑ ℓ ∈ Finset.Ioc k L, ((N+ℓ).divisors.card : ℝ)/2^ℓ) + divisorWindowTail N L := by
  have htail := ((summable_nat_add_iff (k+1)).2 (shifted_half_summable N))
  unfold divisorWindowTail
  rw [← htail.sum_add_tsum_nat_add (L-k)]
  congr 1
  · have hI : Finset.Ioc k L = Finset.Ico (k+1) (L+1) := by
      ext n
      simp only [Finset.mem_Ioc, Finset.mem_Ico]
      omega
    rw [hI, Finset.sum_Ico_eq_sum_range, show L+1-(k+1)=L-k by omega]
    apply Finset.sum_congr rfl
    intro n _
    rw [Nat.add_comm n (k+1)]
  · apply tsum_congr
    intro n
    rw [show n + (L-k) + (k+1) = n+(L+1) by omega]

/-- A simple uniform envelope for the middle contributions returned by the
divisor-progression average. -/
theorem divisor_middle_estimate (k Q : ℕ) (hk : 1 ≤ k) (hQ : 0 < Q)
    (hQmax : Q ≤ 2^(16*k^4)) :
    (∑ ℓ ∈ Finset.Ioc k (k^6),
      (2*(ℓ:ℝ)*(1+Real.log (2*(Q:ℝ)^2))+4) / 2^ℓ) ≤
      72 * (k:ℝ)^16 / 2^k := by
  have hkp : 1 ≤ (k:ℝ) := by exact_mod_cast hk
  have hq : 0 < (Q:ℝ) := by exact_mod_cast hQ
  have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : 0 < (2:ℝ))]
  have hlogQ : Real.log Q ≤ 16*(k:ℝ)^4 := by
    calc
      _ ≤ Real.log ((2:ℝ)^(16*k^4)) :=
        Real.log_le_log hq (by exact_mod_cast hQmax)
      _ = ((16*k^4 : ℕ):ℝ) * Real.log 2 := Real.log_pow _ _
      _ ≤ ((16*k^4 : ℕ):ℝ) * 1 := by gcongr
      _ = _ := by push_cast; ring
  have hk4 : 1 ≤ (k:ℝ)^4 := one_le_pow₀ hkp
  have hlog : 1+Real.log (2*(Q:ℝ)^2) ≤ 34*(k:ℝ)^4 := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    norm_num
    linarith
  have hterm (ℓ : ℕ) (hℓ : ℓ ∈ Finset.Ioc k (k^6)) :
      (2*(ℓ:ℝ)*(1+Real.log (2*(Q:ℝ)^2))+4) / 2^ℓ ≤ 72*(k:ℝ)^10 / 2^k := by
    obtain ⟨h₁,h₂⟩ := Finset.mem_Ioc.1 hℓ
    have h₂' : (ℓ:ℝ) ≤ (k:ℝ)^6 := by exact_mod_cast h₂
    apply div_le_div₀ (by positivity) _ (by positivity) (pow_le_pow_right₀ (by norm_num) h₁.le)
    calc
      _ ≤ 2*(k:ℝ)^6*(34*(k:ℝ)^4)+4 := by
        apply add_le_add_left
        calc
          _ ≤ 2*(ℓ:ℝ)*(34*(k:ℝ)^4) := by gcongr
          _ ≤ _ := by gcongr
      _ ≤ 72*(k:ℝ)^10 := by nlinarith [one_le_pow₀ (n := 10) hkp]
  calc
    _ ≤ ∑ _ℓ ∈ Finset.Ioc k (k^6), 72*(k:ℝ)^10/2^k := Finset.sum_le_sum hterm
    _ = ((k^6-k:ℕ):ℝ) * (72*(k:ℝ)^10/2^k) := by simp
    _ ≤ (k:ℝ)^6 * (72*(k:ℝ)^10/2^k) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast Nat.sub_le (k^6) k
    _ = _ := by ring

/-- The far-tail estimate uniform over the selected representative. -/
theorem divisor_far_estimate (k N Q : ℕ) (hk : 16 ≤ k)
    (hN : N ≤ 2*Q^4) (hQ : Q ≤ 2^(16*k^4)) :
    divisorWindowTail N (k^6) ≤ ((k:ℝ)^6+3) / 2^k := by
  have hk6 : 64*k^4+1+k ≤ k^6 := by
    calc
      _ ≤ 66*k^4 := by
        have h1 : k ≤ k^4 := Nat.le_self_pow (by decide) _
        omega
      _ ≤ k^2*k^4 := by
        exact Nat.mul_le_mul_right _ (by nlinarith)
      _ = k^6 := by ring
  have hN2 : N * 2^k ≤ 2^(k^6) := calc
    N * 2^k ≤ (2*Q^4)*2^k := Nat.mul_le_mul_right _ hN
    _ ≤ (2*(2^(16*k^4))^4)*2^k := by gcongr
    _ = 2^(16*k^4*4)*2*2^k := by rw [pow_mul 2 (16*k^4) 4]; ac_rfl
    _ = 2^(64*k^4+1+k) := by
      rw [← pow_succ, ← pow_add]
      congr 1
      ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide) hk6
  calc
    divisorWindowTail N (k^6) ≤ ((N:ℝ)+(k:ℝ)^6+2) / 2^(k^6) := by
      convert divisor_tail_le N (k^6) using 1
      push_cast
      rfl
    _ = (N:ℝ)/2^(k^6) + ((k:ℝ)^6+2)/2^(k^6) := by ring
    _ ≤ 1 / 2^k + ((k:ℝ)^6+2)/2^k := by
      apply add_le_add
      · apply (div_le_div_iff₀ (by positivity) (by positivity)).2
        simpa only [one_mul] using (show (N:ℝ)*2^k ≤ 2^(k^6) by exact_mod_cast hN2)
      · apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact pow_le_pow_right₀ (by norm_num) (by omega)
    _ = _ := by ring

/-- The resulting precision tends to zero. -/
theorem divisor_window_error_tendsto :
    Tendsto (fun k : ℕ => 72*(k:ℝ)^16/2^k + ((k:ℝ)^6+3)/2^k) atTop (𝓝 0) := by
  have h (m : ℕ) := (summable_pow_mul_geometric_of_norm_lt_one m
    (r := (1/2:ℝ)) (by norm_num)).tendsto_atTop_zero
  have h0 := ((h 16).const_mul 72).add ((h 6).add ((h 0).const_mul 3))
  convert h0 using 1
  · ext k
    simp [inv_pow, div_eq_mul_inv]
    ring
  · norm_num

/-- The sole hypotheses beyond a generic CRT progression are the explicit
finite divisor average and the upper bounds on `Q` and its representative. -/
theorem small_shift_of_window (k N Q : ℕ) (hk : 16 ≤ k)
    (hQ : 0 < Q) (hN : N ≤ 2*Q^4) (hQmax : Q ≤ 2^(16*k^4))
    (hdiv : ∀ j : ℕ, 0 < j → j ≤ k → (2:ℕ)^j ∣ (N+j).divisors.card)
    (hmean : (∑ ℓ ∈ Finset.Ioc k (k^6), ((N+ℓ).divisors.card:ℝ)/2^ℓ) ≤
      ∑ ℓ ∈ Finset.Ioc k (k^6), (2*(ℓ:ℝ)*(1+Real.log (2*(Q:ℝ)^2))+4)/2^ℓ) :
    ∃ z : ℤ, 0 < (2:ℝ)^N * (∑' n : ℕ, (n.divisors.card:ℝ)/(2:ℝ)^n) - z ∧
      (2:ℝ)^N * (∑' n : ℕ, (n.divisors.card:ℝ)/(2:ℝ)^n) - z ≤
        72*(k:ℝ)^16/2^k + ((k:ℝ)^6+3)/2^k := by
  obtain ⟨z,hz⟩ := shift_divisor_series N k hdiv
  refine ⟨z, hz.symm ▸ divisorWindowTail_pos N k, ?_⟩
  rw [hz, divisor_tail_middle N k (k^6) (Nat.le_self_pow (by decide) _)]
  exact add_le_add (hmean.trans (divisor_middle_estimate k Q (by omega) hQ hQmax))
    (divisor_far_estimate k N Q hk hN hQmax)


end Erdos257Readiness

end

section

set_option autoImplicit false

namespace Erdos257Readiness

/-- The height bound in a bounded odd frame remains quartic in the binary
logarithm after adjoining the dyadic modulus. -/
private theorem bounded_frame_height {k A : ℕ} (hk : 2 ≤ k)
    (hA : A ≤ (2 ^ (k * (k + 1)) * (k ^ 6 + 1)) ^ (2 * k ^ 2)) :
    2 ^ k * A ≤ 2 ^ (16 * k ^ 4) := by
  have hkpow : k ^ 6 ≤ 2 ^ (k * 6) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left (Nat.le_of_lt (Nat.lt_two_pow_self (n := k))) _
  have hkpow' : k ^ 6 + 1 ≤ 2 ^ (k * 6 + 1) := by
    rw [pow_succ 2 (k * 6)]
    have := Nat.one_le_two_pow (n := k * 6)
    omega
  have hbase : 2 ^ (k * (k + 1)) * (k ^ 6 + 1) ≤ 2 ^ (k * (k + 1) + (k * 6 + 1)) := by
    rw [pow_add]
    exact Nat.mul_le_mul_left _ hkpow'
  have hdeg : k + (k * (k + 1) + (k * 6 + 1)) * (2 * k ^ 2) ≤ 16 * k ^ 4 := by
    obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hk
    ring_nf
    omega
  calc
    2 ^ k * A ≤ 2 ^ k * (2 ^ (k * (k + 1) + (k * 6 + 1))) ^ (2 * k ^ 2) :=
      Nat.mul_le_mul_left _ (hA.trans (Nat.pow_le_pow_left hbase _))
    _ = 2 ^ (k + (k * (k + 1) + (k * 6 + 1)) * (2 * k ^ 2)) := by rw [← pow_mul, ← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) hdeg

/-- Lift an odd prime frame to a progression all of whose members are
multiples of `2^k`. In the middle window its common divisors with the
progression step come solely from the new dyadic factor, and divide `ℓ`. -/
private theorem lift_odd_frame {k x A : ℕ} (hk : 2 ≤ k) (hA : 0 < A)
    (hx : x < A) (hJ : k ^ 6 + 1 ≤ A)
    (hheight : A ≤ (2 ^ (k * (k + 1)) * (k ^ 6 + 1)) ^ (2 * k ^ 2))
    (hsupp : ∀ p : ℕ, p.Prime → p ∣ A → k ^ 6 < p ∧ ∃ j ∈ Finset.Icc 1 k, p ∣ x + j)
    (hblock : ∀ y : ℕ, ∀ j ∈ Finset.Icc 1 k, 2 ^ j ∣ (x + y * A + j).divisors.card) :
    ∃ Q r : ℕ, 0 < Q ∧ r < Q ∧ 2 ^ k ∣ Q ∧ 2 ^ k ∣ r ∧ k ^ 6 ≤ Q ∧
      Q ≤ 2 ^ (16 * k ^ 4) ∧
      (∀ t j : ℕ, 0 < j → j ≤ k → 2 ^ j ∣ (r + t * Q + j).divisors.card) ∧
      (∀ ℓ : ℕ, k < ℓ → ℓ ≤ k ^ 6 → Nat.gcd Q (r + ℓ) ≤ ℓ) := by
  have hkJ : k ≤ k ^ 6 := Nat.le_self_pow (by decide) _
  have hodd : Nat.Coprime 2 A := Nat.prime_two.coprime_iff_not_dvd.mpr fun h => by
    have := (hsupp 2 Nat.prime_two h).1
    omega
  have hcop := hodd.pow_left k
  let r : ℕ := Nat.chineseRemainder hcop 0 x
  let Q := 2 ^ k * A
  have hr0 : r ≡ 0 [MOD 2 ^ k] := (Nat.chineseRemainder hcop 0 x).property.1
  have hrx : r ≡ x [MOD A] := (Nat.chineseRemainder hcop 0 x).property.2
  have hr : r % A = x := Eq.trans hrx (Nat.mod_eq_of_lt hx)
  have hdecomp : x + A * (r / A) = r := by simpa only [hr] using Nat.mod_add_div r A
  have hpow : 0 < (2 : ℕ) ^ k := by positivity
  have hQA : A ≤ Q := Nat.le_mul_of_pos_left _ hpow
  refine ⟨Q, r, Nat.mul_pos hpow hA, Nat.chineseRemainder_lt_mul hcop 0 x hpow.ne' hA.ne',
    dvd_mul_right _ _, Nat.modEq_zero_iff_dvd.mp hr0, by omega,
    bounded_frame_height hk hheight, ?_, ?_⟩
  · intro t j hj hjk
    have hm : r + t * Q + j = x + (r / A + t * 2 ^ k) * A + j := by
      calc
        _ = (x + A * (r / A)) + t * Q + j := congrArg (fun u => u + t * Q + j) hdecomp.symm
        _ = _ := by dsimp [Q]; ring
    rw [hm]
    exact hblock _ _ (Finset.mem_Icc.mpr ⟨hj, hjk⟩)
  · intro ℓ hkℓ hℓ
    have hc : A.Coprime (r + ℓ) := by
      by_contra hne
      obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hne
      have hpA := hpg.trans (Nat.gcd_dvd_left A (r + ℓ))
      have hprℓ := hpg.trans (Nat.gcd_dvd_right A (r + ℓ))
      obtain ⟨hJp, j, hj, hxj⟩ := hsupp p hp hpA
      have hrj : p ∣ r + j := ((hrx.add_right j).dvd_iff hpA).2 hxj
      have hdiff := Nat.dvd_sub hprℓ hrj
      have hle := (Finset.mem_Icc.mp hj).2
      have heq : r + ℓ - (r + j) = ℓ - j := by omega
      rw [heq] at hdiff
      have := Nat.le_of_dvd (by omega : 0 < ℓ - j) hdiff
      omega
    have hmod : r + ℓ ≡ ℓ [MOD 2 ^ k] := by simpa using hr0.add_right ℓ
    calc
      Nat.gcd Q (r + ℓ) = Nat.gcd (2 ^ k) (r + ℓ) := hc.gcd_mul_right_cancel _
      _ = Nat.gcd (2 ^ k) ℓ := by simpa only [Nat.gcd_comm (2 ^ k)] using hmod.gcd_eq
      _ ≤ ℓ := Nat.gcd_le_right _ (by omega)

/-- For each block length `k ≥ 2`, choose a bounded progression with a
prescribed dyadic divisor, an integral first block and controlled middle gcd. -/
theorem exists_CRT_block (k : ℕ) (hk : 2 ≤ k) :
    ∃ Q r : ℕ, 0 < Q ∧ r < Q ∧ 2 ^ k ∣ Q ∧ 2 ^ k ∣ r ∧ k ^ 6 ≤ Q ∧
      Q ≤ 2 ^ (16 * k ^ 4) ∧
      (∀ t j : ℕ, 0 < j → j ≤ k → 2 ^ j ∣ (r + t * Q + j).divisors.card) ∧
      (∀ ℓ : ℕ, k < ℓ → ℓ ≤ k ^ 6 → Nat.gcd Q (r + ℓ) ≤ ℓ) := by
  obtain ⟨x, A, hA, hx, hJ, hheight, hsupp, hblock⟩ :=
    Erdos249257.exists_bounded_first_block_frame 2 (k ^ 6) k (by decide) (by omega)
      (Nat.le_self_pow (by decide) _)
  exact lift_odd_frame hk hA hx hJ hheight hsupp hblock


end Erdos257Readiness

end

section

set_option autoImplicit false
open Filter Topology
namespace Erdos257Readiness

/-- The CRT progression and the divisor average jointly supply a *positive*
shift, divisible by `2^k`, at controlled height and with a controlled tail. -/
private theorem exists_averaged_shift (k : ℕ) (hk : 2 ≤ k) :
    ∃ N Q : ℕ, 0 < Q ∧ 2 ^ k ∣ N ∧ k ≤ N ∧ N ≤ 2 * Q ^ 4 ∧
      Q ≤ 2 ^ (16 * k ^ 4) ∧ N ≤ 2 ^ (65 * (k + 1) ^ 4) ∧
      (∀ j : ℕ, 0 < j → j ≤ k → 2 ^ j ∣ (N+j).divisors.card) ∧
      (∑ ℓ ∈ Finset.Ioc k (k ^ 6), ((N+ℓ).divisors.card : ℝ) / 2 ^ ℓ) ≤
        ∑ ℓ ∈ Finset.Ioc k (k ^ 6), (2*(ℓ : ℝ)*(1+Real.log (2*(Q : ℝ)^2))+4)/2^ℓ := by
  obtain ⟨Q, r, hQ, hr, hQdiv, hrdiv, hJ, hheight, hblock, hgcd⟩ := exists_CRT_block k hk
  obtain ⟨t, ht, hmean⟩ := exists_small_middle_tail hQ hr hJ hgcd
  let N := r + (t+1) * Q
  have hdiv : 2 ^ k ∣ N := dvd_add hrdiv (dvd_mul_of_dvd_right hQdiv (t+1))
  have hlow : k ≤ N := calc
    k ≤ k ^ 6 := Nat.le_self_pow (by decide) k
    _ ≤ Q := hJ
    _ ≤ (t+1)*Q := Nat.le_mul_of_pos_left _ (by omega)
    _ ≤ N := Nat.le_add_left _ _
  have hQ4 : Q ≤ Q ^ 4 := Nat.le_self_pow (by decide) Q
  have htQ : (t+1) * Q ≤ Q ^ 4 := by
    simpa only [pow_succ Q 3] using Nat.mul_le_mul_right Q (Nat.succ_le_of_lt ht)
  have hsmall : N ≤ 2 * Q ^ 4 := by dsimp [N]; omega
  have hsize : N ≤ 2 ^ (65 * (k+1)^4) := calc
    N ≤ 2 * Q ^ 4 := hsmall
    _ ≤ 2 * (2 ^ (16 * k ^ 4)) ^ 4 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hheight _)
    _ = 2 ^ (1 + (16 * k ^ 4) * 4) := by rw [pow_add 2 1, pow_one, pow_mul 2 (16*k^4) 4]
    _ ≤ 2 ^ (65 * (k+1)^4) := by apply Nat.pow_le_pow_right (by decide); ring_nf; omega
  exact ⟨N, Q, hQ, hdiv, hlow, hsmall, hheight, hsize, hblock (t+1), hmean⟩

/-- Extend eventual shift witnesses to total sequences. Positivity is kept as
well as convergence, so the same sequence witnesses irrationality of the full
sum and return to the integer lattice. -/
private theorem select_small_shifts (E : ℝ) (err : ℕ → ℝ)
    (he : Tendsto err atTop (𝓝 0))
    (h : ∀ k : ℕ, 16 ≤ k → ∃ N : ℕ, ∃ z : ℤ,
      2^k ∣ N ∧ k ≤ N ∧ N ≤ 2^(65*(k+1)^4) ∧
      0 < (2:ℝ)^N * E - z ∧ (2:ℝ)^N * E - z ≤ err k) :
    ∃ (N : ℕ → ℕ) (Z : ℕ → ℤ), (∀ᶠ k in atTop, 2^k ∣ N k) ∧
      (∀ᶠ k in atTop, N k ≤ 2^(65*(k+1)^4)) ∧ Tendsto N atTop atTop ∧
      (∀ᶠ k in atTop, 0 < (2:ℝ)^(N k) * E - Z k) ∧
      Tendsto (fun k => (2:ℝ)^(N k) * E - Z k) atTop (𝓝 0) := by
  classical
  let N (k : ℕ) := if hk : 16 ≤ k then (h k hk).choose else 0
  let Z (k : ℕ) := if hk : 16 ≤ k then (h k hk).choose_spec.choose else 0
  have hall : ∀ᶠ k in atTop, 2^k ∣ N k ∧ k ≤ N k ∧ N k ≤ 2^(65*(k+1)^4) ∧
      0 < (2:ℝ)^(N k) * E - Z k ∧ (2:ℝ)^(N k) * E - Z k ≤ err k := by
    filter_upwards [eventually_ge_atTop 16] with k hk
    simpa only [N, Z, dif_pos hk] using (h k hk).choose_spec.choose_spec
  refine ⟨N, Z, hall.mono fun _ u => u.1, hall.mono fun _ u => u.2.2.1,
    tendsto_atTop_mono' _ (hall.mono fun _ u => u.2.1) tendsto_id,
    hall.mono fun _ u => u.2.2.2.1, ?_⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds he
    (hall.mono fun _ u => u.2.2.2.1.le) (hall.mono fun _ u => u.2.2.2.2)

/-- A single sequence of dyadically aligned shifts takes the full Mersenne
sum to integers from above, with polynomially bounded binary length. -/
theorem exists_full_mersenne_shifts :
    ∃ (N : ℕ → ℕ) (Z : ℕ → ℤ), (∀ᶠ k in atTop, 2^k ∣ N k) ∧
      (∀ᶠ k in atTop, N k ≤ 2^(65*(k+1)^4)) ∧ Tendsto N atTop atTop ∧
      (∀ᶠ k in atTop, 0 < (2:ℝ)^(N k) * fullMersenneSum - Z k) ∧
      Tendsto (fun k => (2:ℝ)^(N k) * fullMersenneSum - Z k) atTop (𝓝 0) := by
  apply select_small_shifts _ _ divisor_window_error_tendsto
  intro k hk
  obtain ⟨N,Q,hQ,hNk,hkN,hNQ,hQmax,hsize,hdiv,hmean⟩ := exists_averaged_shift k (by omega)
  obtain ⟨z,hpos,hub⟩ := small_shift_of_window k N Q hk hQ hNQ hQmax hdiv hmean
  refine ⟨N,z,hNk,hkN,hsize,?_⟩
  simpa only [fullMersenneSum, full_mersenne_eq_divisor_sum] using And.intro hpos hub

/-- Irrationality for all choices of deleted dyadic exponents, proved
using the progression aligned at the CRT step. -/
theorem dyadicDeletion_via_CRT : DyadicDeletionIrrationality := by
  obtain ⟨N,Z,hdiv,hsize,hN,hpos,hbase⟩ := exists_full_mersenne_shifts
  obtain ⟨L,hcut,hL⟩ := cutoffs_of_polynomial_log_height N 65 4 hsize
  exact dyadicDeletion_of_shifts N L Z hdiv hcut hN hL (hpos.mono fun _ h => h.ne') hbase


end Erdos257Readiness

end

theorem solution
    (D : Set ℕ) (hD : D ⊆ Set.range (fun j : ℕ => (2 : ℕ) ^ j)) :
    Irrational (∑' n : {n : ℕ // 0 < n ∧ n ∉ D}, 1 / ((2 : ℝ) ^ n.val - 1)) :=
  Erdos257Readiness.dyadicDeletion_via_CRT D hD

/-
Third-party license for the Will Cook declarations above.
Apache License
Version 2.0, January 2004
http://www.apache.org/licenses/

TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

1. Definitions.

"License" shall mean the terms and conditions for use, reproduction,
and distribution as defined by Sections 1 through 9 of this document.

"Licensor" shall mean the copyright owner or entity authorized by
the copyright owner that is granting the License.

"Legal Entity" shall mean the union of the acting entity and all
other entities that control, are controlled by, or are under common
control with that entity. For the purposes of this definition,
"control" means (i) the power, direct or indirect, to cause the
direction or management of such entity, whether by contract or
otherwise, or (ii) ownership of fifty percent (50%) or more of the
outstanding shares, or (iii) beneficial ownership of such entity.

"You" (or "Your") shall mean an individual or Legal Entity
exercising permissions granted by this License.

"Source" form shall mean the preferred form for making modifications,
including but not limited to software source code, documentation
source, and configuration files.

"Object" form shall mean any form resulting from mechanical
transformation or translation of a Source form, including but
not limited to compiled object code, generated documentation,
and conversions to other media types.

"Work" shall mean the work of authorship, whether in Source or
Object form, made available under the License, as indicated by a
copyright notice that is included in or attached to the work
(an example is provided in the Appendix below).

"Derivative Works" shall mean any work, whether in Source or Object
form, that is based on (or derived from) the Work and for which the
editorial revisions, annotations, elaborations, or other modifications
represent, as a whole, an original work of authorship. For the purposes
of this License, Derivative Works shall not include works that remain
separable from, or merely link (or bind by name) to the interfaces of,
the Work and Derivative Works thereof.

"Contribution" shall mean any work of authorship, including
the original version of the Work and any modifications or additions
to that Work or Derivative Works thereof, that is intentionally
submitted to Licensor for inclusion in the Work by the copyright owner
or by an individual or Legal Entity authorized to submit on behalf of
the copyright owner. For the purposes of this definition, "submitted"
means any form of electronic, verbal, or written communication sent
to the Licensor or its representatives, including but not limited to
communication on electronic mailing lists, source code control systems,
and issue tracking systems that are managed by, or on behalf of, the
Licensor for the purpose of discussing and improving the Work, but
excluding communication that is conspicuously marked or otherwise
designated in writing by the copyright owner as "Not a Contribution."

"Contributor" shall mean Licensor and any individual or Legal Entity
on behalf of whom a Contribution has been received by Licensor and
subsequently incorporated within the Work.

2. Grant of Copyright License. Subject to the terms and conditions of
this License, each Contributor hereby grants to You a perpetual,
worldwide, non-exclusive, no-charge, royalty-free, irrevocable
copyright license to reproduce, prepare Derivative Works of,
publicly display, publicly perform, sublicense, and distribute the
Work and such Derivative Works in Source or Object form.

3. Grant of Patent License. Subject to the terms and conditions of
this License, each Contributor hereby grants to You a perpetual,
worldwide, non-exclusive, no-charge, royalty-free, irrevocable
(except as stated in this section) patent license to make, have made,
use, offer to sell, sell, import, and otherwise transfer the Work,
where such license applies only to those patent claims licensable
by such Contributor that are necessarily infringed by their
Contribution(s) alone or by combination of their Contribution(s)
with the Work to which such Contribution(s) was submitted. If You
institute patent litigation against any entity (including a cross-claim
or counterclaim in a lawsuit) alleging that the Work or a Contribution
incorporated within the Work constitutes direct or contributory patent
infringement, then any patent licenses granted to You under this
License for that Work shall terminate as of the date such litigation
is filed.

4. Redistribution. You may reproduce and distribute copies of the
Work or Derivative Works thereof in any medium, with or without
modifications, and in Source or Object form, provided that You
meet the following conditions:

(a) You must give any other recipients of the Work or
    Derivative Works a copy of this License; and

(b) You must cause any modified files to carry prominent notices
    stating that You changed the files; and

(c) You must retain, in the Source form of any Derivative Works
    that You distribute, all copyright, patent, trademark, and
    attribution notices from the Source form of the Work,
    excluding those notices that do not pertain to any part of
    the Derivative Works; and

(d) If the Work includes a "NOTICE" text file as part of its
    distribution, then any Derivative Works that You distribute must
    include a readable copy of the attribution notices contained
    within such NOTICE file, excluding those notices that do not
    pertain to any part of the Derivative Works, in at least one
    of the following places: within a NOTICE text file distributed
    as part of the Derivative Works; within the Source form or
    documentation, if provided along with the Derivative Works; or,
    within a display generated by the Derivative Works, if and
    wherever such third-party notices normally appear. The contents
    of the NOTICE file are for informational purposes only and
    do not modify the License. You may add Your own attribution
    notices within Derivative Works that You distribute, alongside
    or as an addendum to the NOTICE text from the Work, provided
    that such additional attribution notices cannot be construed
    as modifying the License.

You may add Your own copyright statement to Your modifications and
may provide additional or different license terms and conditions
for use, reproduction, or distribution of Your modifications, or
for any such Derivative Works as a whole, provided Your use,
reproduction, and distribution of the Work otherwise complies with
the conditions stated in this License.

5. Submission of Contributions. Unless You explicitly state otherwise,
any Contribution intentionally submitted for inclusion in the Work
by You to the Licensor shall be under the terms and conditions of
this License, without any additional terms or conditions.
Notwithstanding the above, nothing herein shall supersede or modify
the terms of any separate license agreement you may have executed
with Licensor regarding such Contributions.

6. Trademarks. This License does not grant permission to use the trade
names, trademarks, service marks, or product names of the Licensor,
except as required for reasonable and customary use in describing the
origin of the Work and reproducing the content of the NOTICE file.

7. Disclaimer of Warranty. Unless required by applicable law or
agreed to in writing, Licensor provides the Work (and each
Contributor provides its Contributions) on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
implied, including, without limitation, any warranties or conditions
of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
PARTICULAR PURPOSE. You are solely responsible for determining the
appropriateness of using or redistributing the Work and assume any
risks associated with Your exercise of permissions under this License.

8. Limitation of Liability. In no event and under no legal theory,
whether in tort (including negligence), contract, or otherwise,
unless required by applicable law (such as deliberate and grossly
negligent acts) or agreed to in writing, shall any Contributor be
liable to You for damages, including any direct, indirect, special,
incidental, or consequential damages of any character arising as a
result of this License or out of the use or inability to use the
Work (including but not limited to damages for loss of goodwill,
work stoppage, computer failure or malfunction, or any and all
other commercial damages or losses), even if such Contributor
has been advised of the possibility of such damages.

9. Accepting Warranty or Additional Liability. While redistributing
the Work or Derivative Works thereof, You may choose to offer,
and charge a fee for, acceptance of support, warranty, indemnity,
or other liability obligations and/or rights consistent with this
License. However, in accepting such obligations, You may act only
on Your own behalf and on Your sole responsibility, not on behalf
of any other Contributor, and only if You agree to indemnify,
defend, and hold each Contributor harmless for any liability
incurred by, or claims asserted against, such Contributor by reason
of your accepting any such warranty or additional liability.

END OF TERMS AND CONDITIONS

APPENDIX: How to apply the Apache License to your work.

To apply the Apache License to your work, attach the following
boilerplate notice, with the fields enclosed by brackets "[]"
replaced with your own identifying information. (Don't include
the brackets!)  The text should be enclosed in the appropriate
comment syntax for the file format. We also recommend that a
file or class name and description of purpose be included on the
same "printed page" as the copyright notice for easier
identification within third-party archives.

Copyright [yyyy] [name of copyright owner]

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
