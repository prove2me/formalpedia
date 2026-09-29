-- Prove2me | solution 1 for BlockCycleRotation.sum_diag_isBigO
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:15:41.589391+00:00
-- url     : https://prove2.me/submissions/e1040b64-8ab2-47e1-b403-7ad89d581a18

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_exists_card_divisors_le
import Mathlib

open Real Finset

namespace BlockCycleRotation

@[simp]
theorem remSum_zero (n : ℕ) : remSum n 0 = 0 := by
  rw [remSum]; simp

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

@[simp] theorem K_nil : K [] = 1 := rfl

@[simp] theorem K_singleton (c : ℕ) : K [c] = c := rfl

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

theorem mem_quadruplesQ {n a b a' b' : ℕ} :
    (a, b, a', b') ∈ quadruplesQ n ↔
      (a ≤ n ∧ b ≤ n ∧ a' ≤ n ∧ b' ≤ n) ∧ 1 ≤ a' ∧ a' < a ∧ 1 ≤ b' ∧ b' < b
        ∧ n = a * b + a' * b' := by
  simp [quadruplesQ, Finset.mem_filter, Finset.mem_product, and_assoc]

theorem diag_card_le {n : ℕ} (hn : 0 < n) :
    ((quadruplesQ n).filter (fun q => q.1 = q.2.1)).card
      ≤ ∑ a ∈ Finset.range (Nat.sqrt n + 1), (n - a * a).divisors.card := by
  rw [← Finset.card_sigma]
  refine Finset.card_le_card_of_injOn
    (fun q => (⟨q.1, q.2.2.1⟩ : (_ : ℕ) × ℕ)) ?_ ?_
  · rintro ⟨a, b, a', b'⟩ hq
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hq
    obtain ⟨hmem, hab⟩ := hq
    obtain ⟨-, ha1, ha2, hb1, hb2, hsum⟩ := mem_quadruplesQ.1 hmem
    have hba : b = a := hab.symm
    subst hba
    have hbb : 1 ≤ a' * b' := Nat.one_le_iff_ne_zero.2 (by positivity)
    have hlt : b * b < n := by omega
    have hsq : b ≤ Nat.sqrt n := Nat.le_sqrt.2 (by omega)
    have hdvd : a' ∣ n - b * b := ⟨b', by omega⟩
    have hne : n - b * b ≠ 0 := by omega
    simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_range, Nat.mem_divisors]
    exact ⟨Nat.lt_succ_of_le hsq, hdvd, hne⟩
  · rintro ⟨a, b, a', b'⟩ hq ⟨c, e, c', e'⟩ hr heq
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hq hr
    obtain ⟨hmem, hab⟩ := hq
    obtain ⟨hmem2, hce⟩ := hr
    obtain ⟨-, ha1, ha2, hb1, hb2, hsum⟩ := mem_quadruplesQ.1 hmem
    obtain ⟨-, hc1, hc2, he1, he2, hsum2⟩ := mem_quadruplesQ.1 hmem2
    simp only [Sigma.mk.injEq] at heq
    obtain ⟨h1, h2⟩ := heq
    subst h1
    have h2' : a' = c' := eq_of_heq h2
    subst h2'
    have hb : b = a := hab.symm
    have he : e = a := hce.symm
    subst hb
    subst he
    have : a' * b' = a' * e' := by omega
    have : b' = e' := Nat.eq_of_mul_eq_mul_left (by omega) this
    subst this
    rfl

theorem sum_diag_le {n : ℕ} (hn : 0 < n) :
    ∑ q ∈ (quadruplesQ n).filter (fun q => q.1 = q.2.1), q.1
      ≤ Nat.sqrt n * ∑ a ∈ Finset.range (Nat.sqrt n + 1), (n - a * a).divisors.card := by
  have hterm : ∀ q ∈ (quadruplesQ n).filter (fun q => q.1 = q.2.1), q.1 ≤ Nat.sqrt n := by
    rintro ⟨a, b, a', b'⟩ hq
    simp only [Finset.mem_filter] at hq
    obtain ⟨hmem, hab⟩ := hq
    obtain ⟨-, ha1, ha2, hb1, hb2, hsum⟩ := mem_quadruplesQ.1 hmem
    have hba : b = a := hab.symm
    subst hba
    have hbb : 1 ≤ a' * b' := Nat.one_le_iff_ne_zero.2 (by positivity)
    have hsq : b ≤ Nat.sqrt n := Nat.le_sqrt.2 (by omega)
    exact hsq
  calc ∑ q ∈ (quadruplesQ n).filter (fun q => q.1 = q.2.1), q.1
      ≤ ∑ _q ∈ (quadruplesQ n).filter (fun q => q.1 = q.2.1), Nat.sqrt n :=
        Finset.sum_le_sum hterm
    _ = ((quadruplesQ n).filter (fun q => q.1 = q.2.1)).card * Nat.sqrt n := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (∑ a ∈ Finset.range (Nat.sqrt n + 1), (n - a * a).divisors.card) * Nat.sqrt n :=
        Nat.mul_le_mul_right _ (diag_card_le hn)
    _ = Nat.sqrt n * _ := Nat.mul_comm _ _

end BlockCycleRotation

open BlockCycleRotation in
/-- **The diagonal is `O(n^{1+ε})`.**  This is the term the paper discards
after symmetrising. -/
theorem solution {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      ((∑ q ∈ (quadruplesQ n).filter (fun q => q.1 = q.2.1), q.1 : ℕ) : ℝ)
        ≤ C * (n : ℝ) ^ (1 + ε):= by
  obtain ⟨C0, hC0, hCd⟩ := exists_card_divisors_le hε
  refine ⟨2 * C0, by positivity, fun n hn => ?_⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hnε : (0 : ℝ) ≤ (n : ℝ) ^ ε := by positivity
  -- each divisor count is at most `C₀ n^ε`
  have hterm : ∀ a ∈ Finset.range (Nat.sqrt n + 1),
      (((n - a * a).divisors.card : ℕ) : ℝ) ≤ C0 * (n : ℝ) ^ ε := by
    intro a _
    rcases Nat.eq_zero_or_pos (n - a * a) with h0 | h0
    · rw [h0]
      simp
      positivity
    · refine (hCd _ h0.ne').trans ?_
      have hle : ((n - a * a : ℕ) : ℝ) ≤ (n : ℝ) := by
        have : (n - a * a : ℕ) ≤ n := Nat.sub_le _ _
        exact_mod_cast this
      have := Real.rpow_le_rpow (by positivity) hle hε.le
      nlinarith
  have hS : ((∑ a ∈ Finset.range (Nat.sqrt n + 1), (n - a * a).divisors.card : ℕ) : ℝ)
      ≤ ((Nat.sqrt n : ℝ) + 1) * (C0 * (n : ℝ) ^ ε) := by
    push_cast
    calc ∑ a ∈ Finset.range (Nat.sqrt n + 1), (((n - a * a).divisors.card : ℕ) : ℝ)
        ≤ ∑ _a ∈ Finset.range (Nat.sqrt n + 1), C0 * (n : ℝ) ^ ε :=
          Finset.sum_le_sum hterm
      _ = ((Nat.sqrt n : ℝ) + 1) * (C0 * (n : ℝ) ^ ε) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  -- the natural-number bound
  have hnat := sum_diag_le hn
  have hcast : ((∑ q ∈ (quadruplesQ n).filter (fun q => q.1 = q.2.1), q.1 : ℕ) : ℝ)
      ≤ (Nat.sqrt n : ℝ)
        * ((∑ a ∈ Finset.range (Nat.sqrt n + 1), (n - a * a).divisors.card : ℕ) : ℝ) := by
    exact_mod_cast hnat
  -- `√n · (√n + 1) ≤ 2n`
  have hsq1 : (Nat.sqrt n : ℝ) * (Nat.sqrt n : ℝ) ≤ (n : ℝ) := by
    have h : Nat.sqrt n * Nat.sqrt n ≤ n := by
      have h2 := Nat.sqrt_le' n
      rwa [pow_two] at h2
    exact_mod_cast h
  have hsq2 : (Nat.sqrt n : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.sqrt_le_self n
  have hsqnn : (0 : ℝ) ≤ (Nat.sqrt n : ℝ) := by positivity
  have hrpow : (n : ℝ) ^ (1 + ε) = (n : ℝ) * (n : ℝ) ^ ε := by
    rw [Real.rpow_add hn', Real.rpow_one]
  rw [hrpow]
  have hmid : (Nat.sqrt n : ℝ)
      * ((∑ a ∈ Finset.range (Nat.sqrt n + 1), (n - a * a).divisors.card : ℕ) : ℝ)
      ≤ (Nat.sqrt n : ℝ) * (((Nat.sqrt n : ℝ) + 1) * (C0 * (n : ℝ) ^ ε)) :=
    mul_le_mul_of_nonneg_left hS hsqnn
  nlinarith [hcast, hmid, hsq1, hsq2, hnε, hC0.le]
