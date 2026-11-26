-- Prove2me | solution 1 for Erdos287.cofactor_adic_period
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T11:51:30.154637+00:00
-- url     : https://prove2.me/submissions/26896a79-6c5e-4ea2-b45f-78ff13b4b2f2

import Mathlib

open Finset

set_option autoImplicit false
set_option maxHeartbeats 1500000

private theorem norm_reciprocal_nat {p n : ℕ} [Fact p.Prime] (hn : n ≠ 0) :
    padicNorm p ((1 : ℚ) / n) = (p : ℚ) ^ padicValNat p n := by
  have hq : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [one_div, padicNorm.eq_zpow_of_nonzero (inv_ne_zero hq), padicValRat.inv,
    padicValRat.of_nat, neg_neg, zpow_natCast]

private theorem norm_reciprocal_le_of_not_dvd {p h n : ℕ} [Fact p.Prime]
    (hn : 0 < n) (hd : ¬ p ^ (h + 1) ∣ n) :
    padicNorm p ((1 : ℚ) / n) ≤ (p : ℚ) ^ h := by
  have hp : p.Prime := Fact.out
  have hpQ : (1 : ℚ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hv : padicValNat p n ≤ h := by
    have hnot := mt ((padicValNat_dvd_iff_le hn.ne').mpr) hd
    omega
  rw [norm_reciprocal_nat hn.ne']
  exact pow_le_pow_right₀ hpQ hv

private theorem no_admissible_sum_at_unique_deep_offset {p : ℕ} [Fact p.Prime]
    (T : Finset ℕ) (h c : ℕ) (hc : 0 < c)
    (hw : ∀ a ∈ T, ∀ b ∈ T, a < b + p ^ (h + 1))
    (hdeep : ∃ a ∈ T, p ^ (h + 1) ∣ c + a) :
    ¬ padicNorm p (∑ d ∈ T, (1 : ℚ) / ((c + d : ℕ) : ℚ)) ≤ (p : ℚ)⁻¹ := by
  obtain ⟨a, ha, hda⟩ := hdeep
  have hp : p.Prime := Fact.out
  have hpQ : (1 : ℚ) < p := by exact_mod_cast hp.one_lt
  have hunique (b : ℕ) (hb : b ∈ T.erase a) : ¬ p ^ (h + 1) ∣ c + b := by
    intro hdb
    have hbT := mem_of_mem_erase hb
    rcases lt_or_gt_of_ne (ne_of_mem_erase hb) with hab | hab
    · have hd : p ^ (h + 1) ∣ a - b := by
        rw [← show c + a - (c + b) = a - b by omega]
        exact Nat.dvd_sub hda hdb
      have ht := Nat.le_of_dvd (by omega : 0 < a - b) hd
      have hu := hw a ha b hbT
      omega
    · have hd : p ^ (h + 1) ∣ b - a := by
        rw [← show c + b - (c + a) = b - a by omega]
        exact Nat.dvd_sub hdb hda
      have ht := Nat.le_of_dvd (by omega : 0 < b - a) hd
      have hu := hw b hbT a ha
      omega
  have hrest : padicNorm p (∑ d ∈ T.erase a, (1 : ℚ) / ((c + d : ℕ) : ℚ)) ≤ (p : ℚ) ^ h := by
    apply padicNorm.sum_le' _ (by positivity)
    intro b hb
    exact norm_reciprocal_le_of_not_dvd (by omega : 0 < c + b) (hunique b hb)
  have hv := (padicValNat_dvd_iff_le (by omega : c + a ≠ 0)).mp hda
  have hlarge : (p : ℚ) ^ h < padicNorm p ((1 : ℚ) / ((c + a : ℕ) : ℚ)) := by
    rw [norm_reciprocal_nat (by omega : c + a ≠ 0)]
    exact pow_lt_pow_right₀ hpQ (by omega)
  have hlt := hrest.trans_lt hlarge
  have hsum := sum_erase_add T (fun d => (1 : ℚ) / ((c + d : ℕ) : ℚ)) ha
  have hbig : (p : ℚ)⁻¹ < (p : ℚ) ^ h :=
    (inv_lt_one_of_one_lt₀ hpQ).trans_le (one_le_pow₀ hpQ.le)
  rw [← hsum, padicNorm.add_eq_max_of_ne hlt.ne, max_eq_right hlt.le]
  exact (hbig.trans hlarge).not_ge

private theorem norm_cofactor_sum_of_representation {p : ℕ} [Fact p.Prime]
    (D T : Finset ℕ) (e c : ℕ) (he : 1 ≤ e) (hc : 0 < c)
    (hpos : ∀ n ∈ D, 0 < n) (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1)
    (hshape : T.image (fun d => (c + d) * p ^ e) = D.filter (fun n => p ^ e ∣ n)) :
    padicNorm p (∑ d ∈ T, (1 : ℚ) / ((c + d : ℕ) : ℚ)) ≤ (p : ℚ)⁻¹ := by
  have hp : p.Prime := Fact.out
  have hpQ : (0 : ℚ) < p := by exact_mod_cast hp.pos
  have hpone : (1 : ℚ) ≤ p := by exact_mod_cast hp.one_lt.le
  let q := p ^ e
  let A := ∑ n ∈ D.filter (fun n => q ∣ n), (1 : ℚ) / n
  let B := ∑ n ∈ D.filter (fun n => ¬ q ∣ n), (1 : ℚ) / n
  have hq : 0 < q := pow_pos hp.pos e
  have hAB : A + B = 1 :=
    (sum_filter_add_sum_filter_not D (fun n => q ∣ n) (fun n => (1 : ℚ) / n)).trans hsum
  have hB : padicNorm p B ≤ (p : ℚ) ^ (e - 1) := by
    apply padicNorm.sum_le' _ (by positivity)
    intro n hn
    obtain ⟨hnD, hd⟩ := mem_filter.mp hn
    have hposN := hpos n hnD
    have hv : padicValNat p n ≤ e - 1 := by
      have hnot := mt ((padicValNat_dvd_iff_le hposN.ne').mpr) hd
      omega
    rw [norm_reciprocal_nat hposN.ne']
    exact pow_le_pow_right₀ hpone hv
  have hA : padicNorm p A ≤ (p : ℚ) ^ (e - 1) := by
    rw [eq_sub_of_add_eq hAB]
    exact padicNorm.sub.trans (max_le (by rw [padicNorm.one]; exact one_le_pow₀ hpone) hB)
  have hscale : (∑ d ∈ T, (1 : ℚ) / ((c + d : ℕ) : ℚ)) = ((p : ℚ) ^ e) * A := by
    change T.image (fun d => (c + d) * q) = D.filter (fun n => q ∣ n) at hshape
    change _ = ((p : ℚ) ^ e) * (∑ n ∈ D.filter (fun n => q ∣ n), (1 : ℚ) / n)
    rw [← hshape, sum_image (fun a _ b _ hab =>
      Nat.add_left_cancel (Nat.eq_of_mul_eq_mul_right hq hab)), mul_sum]
    apply sum_congr rfl
    intro d _
    have hcd : (0 : ℚ) < (c : ℚ) + d := by exact_mod_cast (by omega : 0 < c + d)
    have hneq : ((p : ℚ) ^ e) ≠ 0 := (pow_pos hpQ _).ne'
    simp only [q, Nat.cast_mul, Nat.cast_pow, Nat.cast_add]
    field_simp [hcd.ne', hneq]
  have hnorm : padicNorm p ((p : ℚ) ^ e) = (p : ℚ) ^ (-(e : ℤ)) := by
    have hn : ((p ^ e : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (pow_ne_zero e hp.ne_zero)
    rw [← Nat.cast_pow, padicNorm.eq_zpow_of_nonzero hn, padicValRat.of_nat, padicValNat.prime_pow]
  rw [hscale, padicNorm.mul, hnorm]
  calc
    _ ≤ (p : ℚ) ^ (-(e : ℤ)) * (p : ℚ) ^ (e - 1) :=
      mul_le_mul_of_nonneg_left hA (zpow_nonneg hpQ.le _)
    _ = _ := by
      rw [← zpow_natCast, ← zpow_add₀ hpQ.ne', ← zpow_neg_one]
      congr 1
      omega

/-- The full arithmetic condition on a translated cofactor pattern is
periodic once the valuation of a single denominator would isolate it. -/
theorem solution (p : ℕ) (hp : p.Prime) :
    (∀ (D T : Finset ℕ) (e c : ℕ), 1 ≤ e → 0 < c →
      (∀ n ∈ D, 0 < n) → (∑ n ∈ D, (1 : ℚ) / n = 1) →
      T.image (fun d => (c + d) * p ^ e) = D.filter (fun n => p ^ e ∣ n) →
      padicNorm p (∑ d ∈ T, (1 : ℚ) / ((c + d : ℕ) : ℚ)) ≤ (p : ℚ)⁻¹) ∧
    ∀ (T : Finset ℕ) (h c c' : ℕ), 0 < c → 0 < c' →
      (∀ a ∈ T, ∀ b ∈ T, a < b + p ^ (h + 1)) →
      c ≡ c' [MOD p ^ (2 * h + 1)] →
      (padicNorm p (∑ d ∈ T, (1 : ℚ) / ((c + d : ℕ) : ℚ)) ≤ (p : ℚ)⁻¹ ↔
       padicNorm p (∑ d ∈ T, (1 : ℚ) / ((c' + d : ℕ) : ℚ)) ≤ (p : ℚ)⁻¹) := by
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨norm_cofactor_sum_of_representation (p := p), ?_⟩
  intro T h c c' hc hc' hw hshift
  let q := p ^ (h + 1)
  have hshift' : c ≡ c' [MOD q] :=
    hshift.of_dvd (pow_dvd_pow p (by omega : h + 1 ≤ 2 * h + 1))
  have hsame (d : ℕ) : q ∣ c + d ↔ q ∣ c' + d := by
    rw [← Nat.modEq_zero_iff_dvd, ← Nat.modEq_zero_iff_dvd]
    exact ⟨fun hd => (hshift'.add_right d).symm.trans hd,
      fun hd => (hshift'.add_right d).trans hd⟩
  by_cases hhigh : ∃ d ∈ T, q ∣ c + d
  · have hhigh' : ∃ d ∈ T, q ∣ c' + d := by
      obtain ⟨d, hd, hq⟩ := hhigh
      exact ⟨d, hd, (hsame d).mp hq⟩
    exact ⟨fun hn => (no_admissible_sum_at_unique_deep_offset T h c hc hw hhigh hn).elim,
      fun hn => (no_admissible_sum_at_unique_deep_offset T h c' hc' hw hhigh' hn).elim⟩
  have hpQ : (0 : ℚ) < p := by exact_mod_cast hp.pos
  let δ : ℤ := (c' : ℤ) - (c : ℤ)
  have hδ : ((p ^ (2 * h + 1) : ℕ) : ℤ) ∣ δ := hshift.dvd
  have hnδ := (padicNorm.dvd_iff_norm_le (p := p) (n := 2 * h + 1) (z := δ)).mp hδ
  let f (d : ℕ) : ℚ := (1 : ℚ) / ((c + d : ℕ) : ℚ)
  let g (d : ℕ) : ℚ := (1 : ℚ) / ((c' + d : ℕ) : ℚ)
  have hpoint (d : ℕ) (hd : d ∈ T) : padicNorm p (f d - g d) ≤ (p : ℚ)⁻¹ := by
    have hnot : ¬ q ∣ c + d := fun h => hhigh ⟨d, hd, h⟩
    have hf : padicNorm p (f d) ≤ (p : ℚ) ^ h :=
      norm_reciprocal_le_of_not_dvd (by omega : 0 < c + d) hnot
    have hg : padicNorm p (g d) ≤ (p : ℚ) ^ h :=
      norm_reciprocal_le_of_not_dvd (by omega : 0 < c' + d) ((hsame d).not.mp hnot)
    have heq : f d - g d = (δ : ℚ) * f d * g d := by
      have h1 : (0 : ℚ) < (c : ℚ) + d := by exact_mod_cast (by omega : 0 < c + d)
      have h2 : (0 : ℚ) < (c' : ℚ) + d := by exact_mod_cast (by omega : 0 < c' + d)
      dsimp only [f, g, δ]
      push_cast
      field_simp [h1.ne', h2.ne'] <;> ring
    rw [heq, padicNorm.mul, padicNorm.mul]
    calc
      _ ≤ (p : ℚ) ^ (-((2 * h + 1 : ℕ) : ℤ)) * (p : ℚ) ^ h * (p : ℚ) ^ h :=
        mul_le_mul (mul_le_mul hnδ hf (padicNorm.nonneg _) (zpow_nonneg hpQ.le _))
          hg (padicNorm.nonneg _) (mul_nonneg (zpow_nonneg hpQ.le _) (by positivity))
      _ = _ := by
        rw [← zpow_natCast, ← zpow_add₀ hpQ.ne', ← zpow_add₀ hpQ.ne', ← zpow_neg_one]
        congr 1
        push_cast
        ring
  let S : ℚ := ∑ d ∈ T, f d
  let S' : ℚ := ∑ d ∈ T, g d
  have hdiff : padicNorm p (S - S') ≤ (p : ℚ)⁻¹ := by
    change padicNorm p ((∑ d ∈ T, f d) - ∑ d ∈ T, g d) ≤ _
    rw [← sum_sub_distrib]
    exact padicNorm.sum_le' hpoint (by positivity)
  change padicNorm p S ≤ (p : ℚ)⁻¹ ↔ padicNorm p S' ≤ (p : ℚ)⁻¹
  constructor
  · intro hs
    rw [show S' = S - (S - S') by ring]
    exact padicNorm.sub.trans (max_le hs hdiff)
  · intro hs'
    rw [show S = (S - S') + S' by ring]
    exact padicNorm.nonarchimedean.trans (max_le hdiff hs')

