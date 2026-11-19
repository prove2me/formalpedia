-- Prove2me | solution 1 for Erdos195.safe_word_composition
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-18T19:40:29.995676+00:00
-- url     : https://prove2.me/submissions/1d23afa0-2f28-401b-85e5-8354edb2adcb

import Definitions.Def_Erdos195_tree
import Theorems.Thm_Erdos195_exists_treeLt_safe_iff
import Theorems.Thm_Erdos195_treeLt_order_props
import Mathlib.Data.List.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Erdos195

private lemma instPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private def lift (m : ℕ) (s x : ℤ) : ℤ := s + (2 : ℤ) ^ m * x

private def liftBlock (m : ℕ) (A : ℤ → List ℤ) (s : ℤ) : List ℤ :=
  (A s).map (fun x => lift m s x)

private def composeWord (m : ℕ) (A : ℤ → List ℤ) (residues : List ℤ) : List ℤ :=
  (residues.map (liftBlock m A)).flatten

private lemma bitOne_flip {x y : ℤ} (h : x ≠ y) :
    bitOne y (padicValInt 2 (y - x)) ↔ ¬ bitOne x (padicValInt 2 (y - x)) := by
  haveI := instPrimeTwo
  set k := padicValInt 2 (y - x)
  have hne : y - x ≠ 0 := sub_ne_zero.mpr h.symm
  have hdvd : (2 : ℤ) ^ k ∣ y - x := padicValInt_dvd (p := 2) (y - x)
  have hndvd : ¬ (2 : ℤ) ^ (k + 1) ∣ y - x := by
    intro hpow
    have hk : k + 1 ≤ padicValInt 2 (y - x) :=
      ((padicValInt_dvd_iff (p := 2) (k + 1) (y - x)).mp hpow).resolve_left hne
    omega
  obtain ⟨mm, hm⟩ := hdvd
  have hmodd : ¬ (2 : ℤ) ∣ mm := by
    intro h2
    obtain ⟨t, ht⟩ := h2
    refine hndvd ⟨t, ?_⟩
    rw [hm, ht, pow_succ]
    ring
  have hy : y = x + 2 ^ k * mm := by omega
  have hpow0 : (2 : ℤ) ^ k ≠ 0 := pow_ne_zero _ (by decide)
  have hpowpos : (0 : ℤ) < 2 ^ k := pow_pos (by decide) k
  have hxdecomp : x % 2 ^ k + (x / 2 ^ k) * 2 ^ k = x := Int.emod_add_ediv_mul x (2 ^ k)
  have hydecomp : x % 2 ^ k + (x / 2 ^ k + mm) * 2 ^ k = y := by
    calc
      x % 2 ^ k + (x / 2 ^ k + mm) * 2 ^ k
          = x % 2 ^ k + (x / 2 ^ k) * 2 ^ k + mm * 2 ^ k := by ring
      _ = x + mm * 2 ^ k := by rw [hxdecomp]
      _ = x + 2 ^ k * mm := by ring
      _ = y := hy.symm
  have hydecomp' : x % 2 ^ k + 2 ^ k * (x / 2 ^ k + mm) = y := by
    rw [← hydecomp]
    ring
  have hrmod0 : 0 ≤ x % 2 ^ k := Int.emod_nonneg _ hpow0
  have hrmod1 : x % 2 ^ k < 2 ^ k := Int.emod_lt_of_pos _ hpowpos
  have hquot : y / 2 ^ k = x / 2 ^ k + mm := by
    have hunq := (Int.ediv_emod_unique (a := y) (b := (2 : ℤ) ^ k) (r := x % 2 ^ k)
      (q := x / 2 ^ k + mm) hpowpos).2
    exact (hunq ⟨hydecomp', hrmod0, hrmod1⟩).1
  have hm1 : mm % 2 = 1 := by
    rcases Int.emod_two_eq mm with hm0 | hm1
    · exact (hmodd (Int.dvd_of_emod_eq_zero hm0)).elim
    · exact hm1
  have hadd : (x / 2 ^ k + mm) % 2 = (x / 2 ^ k % 2 + mm % 2) % 2 := Int.add_emod _ _ _
  simp only [bitOne, hquot]
  rcases Int.emod_two_eq (x / 2 ^ k) with hx0 | hx1
  · simp [hx0, hm1, hadd]
  · simp [hx1, hm1, hadd]

private lemma pv2_pow (m : ℕ) : padicValInt 2 ((2 : ℤ) ^ m) = m := by
  haveI := instPrimeTwo
  induction m with
  | zero =>
    simp
  | succ m ih =>
    rw [pow_succ, padicValInt.mul (pow_ne_zero _ (by decide)) (by decide), ih]
    have : padicValInt 2 (2 : ℤ) = 1 := padicValInt_self
    omega

private lemma pv2_pow_mul {m : ℕ} {d : ℤ} (hd : d ≠ 0) :
    padicValInt 2 ((2 : ℤ) ^ m * d) = m + padicValInt 2 d := by
  haveI := instPrimeTwo
  rw [padicValInt.mul (pow_ne_zero _ (by decide)) hd, pv2_pow]

private lemma two_pow_pos (m : ℕ) : (0 : ℤ) < (2 : ℤ) ^ m :=
  pow_pos (by decide) m

private lemma two_pow_ne_zero (m : ℕ) : (2 : ℤ) ^ m ≠ 0 :=
  pow_ne_zero _ (by decide)

private lemma emod_ediv_eq (a b : ℤ) :
    a = a % b + b * (a / b) := by
  calc
    a = a % b + (a / b) * b := (Int.emod_add_ediv_mul a b).symm
    _ = a % b + b * (a / b) := by ring

private lemma lift_inj {m : ℕ} {s t x y : ℤ}
    (hs0 : 0 ≤ s) (hs1 : s < (2 : ℤ) ^ m)
    (ht0 : 0 ≤ t) (ht1 : t < (2 : ℤ) ^ m)
    (h : lift m s x = lift m t y) : s = t ∧ x = y := by
  have heq : s = t + (2 : ℤ) ^ m * (y - x) := by
    simp only [lift] at h
    have : s = t + (2 : ℤ) ^ m * y - (2 : ℤ) ^ m * x := by linarith
    rw [this]
    ring
  have hsmod : s % (2 : ℤ) ^ m = s := Int.emod_eq_of_lt hs0 hs1
  have htmod : t % (2 : ℤ) ^ m = t := Int.emod_eq_of_lt ht0 ht1
  have hcongr : s % (2 : ℤ) ^ m = t % (2 : ℤ) ^ m := by
    rw [heq, Int.add_mul_emod_self_left]
  have hst : s = t := by
    calc
      s = s % (2 : ℤ) ^ m := hsmod.symm
      _ = t % (2 : ℤ) ^ m := hcongr
      _ = t := htmod
  refine ⟨hst, ?_⟩
  subst hst
  have hxy : (2 : ℤ) ^ m * x = (2 : ℤ) ^ m * y := by
    simp only [lift] at h
    linarith
  exact mul_left_cancel₀ (two_pow_ne_zero m) hxy

private lemma lift_inj_same {m : ℕ} {s x y : ℤ} (h : lift m s x = lift m s y) : x = y := by
  have : (2 : ℤ) ^ m * x = (2 : ℤ) ^ m * y := by
    simp only [lift] at h
    linarith
  exact mul_left_cancel₀ (two_pow_ne_zero m) this

private lemma lift_two {m : ℕ} {s a b : ℤ} :
    lift m s (2 * b - a) = 2 * lift m s b - lift m s a := by
  simp [lift]
  ring

private lemma lift_three {m : ℕ} {s a b : ℤ} :
    lift m s (3 * b - 2 * a) = 3 * lift m s b - 2 * lift m s a := by
  simp [lift]
  ring

private lemma lift_sub {m : ℕ} {s t x y : ℤ} :
    lift m t y - lift m s x = t - s + (2 : ℤ) ^ m * (y - x) := by
  simp [lift]
  ring

private lemma emod_pow_of_le {a : ℤ} {k m : ℕ} (hk : k ≤ m) :
    (a % (2 : ℤ) ^ m) % (2 : ℤ) ^ k = a % (2 : ℤ) ^ k := by
  have hdvd : (2 : ℤ) ^ k ∣ (2 : ℤ) ^ m := pow_dvd_pow _ hk
  rw [Int.emod_def a ((2 : ℤ) ^ m)]
  have hz : ((2 : ℤ) ^ m * (a / (2 : ℤ) ^ m)) % (2 : ℤ) ^ k = 0 :=
    Int.dvd_iff_emod_eq_zero.mp (dvd_mul_of_dvd_left hdvd _)
  rw [Int.sub_emod, hz, sub_zero, Int.emod_emod]

private lemma lift_low_decomp {m k : ℕ} {s x : ℤ} (hk : k < m) :
    lift m s x =
      s % (2 : ℤ) ^ k + (2 : ℤ) ^ k * (s / (2 : ℤ) ^ k + (2 : ℤ) ^ (m - k) * x) := by
  have hmk : m = k + (m - k) := (Nat.add_sub_of_le (Nat.le_of_lt hk)).symm
  have hpowm : (2 : ℤ) ^ m = (2 : ℤ) ^ k * (2 : ℤ) ^ (m - k) := by
    rw [← pow_add, ← hmk]
  have hsdecomp : s = s % (2 : ℤ) ^ k + (2 : ℤ) ^ k * (s / (2 : ℤ) ^ k) :=
    emod_ediv_eq s ((2 : ℤ) ^ k)
  simp only [lift, hpowm]
  conv_lhs => rw [hsdecomp]
  ring

private lemma emod_lift_low {m k : ℕ} {s x : ℤ}
    (hs0 : 0 ≤ s) (hs1 : s < (2 : ℤ) ^ m) (hk : k < m) :
    lift m s x % (2 : ℤ) ^ k = s % (2 : ℤ) ^ k := by
  have hpowk := two_pow_pos k
  have hdecomp := lift_low_decomp (s := s) (x := x) hk
  have hr0 : 0 ≤ s % (2 : ℤ) ^ k := Int.emod_nonneg _ (two_pow_ne_zero k)
  have hr1 : s % (2 : ℤ) ^ k < (2 : ℤ) ^ k := Int.emod_lt_of_pos _ hpowk
  exact ((Int.ediv_emod_unique (a := lift m s x) (b := (2 : ℤ) ^ k)
      (r := s % (2 : ℤ) ^ k)
      (q := s / (2 : ℤ) ^ k + (2 : ℤ) ^ (m - k) * x) hpowk).mpr
    ⟨hdecomp.symm, hr0, hr1⟩).2

private lemma bitOne_lift_low {m k : ℕ} {s x : ℤ}
    (hs0 : 0 ≤ s) (hs1 : s < (2 : ℤ) ^ m) (hk : k < m) :
    bitOne (lift m s x) k ↔ bitOne s k := by
  have hpowk := two_pow_pos k
  have hdecomp := lift_low_decomp (s := s) (x := x) hk
  have hr0 : 0 ≤ s % (2 : ℤ) ^ k := Int.emod_nonneg _ (two_pow_ne_zero k)
  have hr1 : s % (2 : ℤ) ^ k < (2 : ℤ) ^ k := Int.emod_lt_of_pos _ hpowk
  have hquot : lift m s x / (2 : ℤ) ^ k =
      s / (2 : ℤ) ^ k + (2 : ℤ) ^ (m - k) * x :=
    ((Int.ediv_emod_unique (a := lift m s x) (b := (2 : ℤ) ^ k)
        (r := s % (2 : ℤ) ^ k)
        (q := s / (2 : ℤ) ^ k + (2 : ℤ) ^ (m - k) * x) hpowk).mpr
      ⟨hdecomp.symm, hr0, hr1⟩).1
  have hmkpos : 1 ≤ m - k := Nat.succ_le_iff.mpr (Nat.sub_pos_of_lt hk)
  have heven : ((2 : ℤ) ^ (m - k) * x) % 2 = 0 := by
    have hfac : (2 : ℤ) ^ (m - k) = 2 * (2 : ℤ) ^ (m - k - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [hfac, mul_assoc, Int.mul_emod_right]
  have hsum : (s / (2 : ℤ) ^ k + (2 : ℤ) ^ (m - k) * x) % 2 =
      (s / (2 : ℤ) ^ k % 2 + ((2 : ℤ) ^ (m - k) * x) % 2) % 2 := Int.add_emod _ _ _
  simp [bitOne, hquot, hsum, heven]

private lemma lift_high_decomp {m k : ℕ} {s x : ℤ} :
    lift m s x =
      (s + (2 : ℤ) ^ m * (x % (2 : ℤ) ^ k)) +
        (2 : ℤ) ^ (m + k) * (x / (2 : ℤ) ^ k) := by
  have hpowadd : (2 : ℤ) ^ (m + k) = (2 : ℤ) ^ m * (2 : ℤ) ^ k := pow_add _ _ _
  have hx : x = x % (2 : ℤ) ^ k + (2 : ℤ) ^ k * (x / (2 : ℤ) ^ k) :=
    emod_ediv_eq x ((2 : ℤ) ^ k)
  simp only [lift]
  conv_lhs => rw [hx]
  rw [hpowadd]
  ring

private lemma lift_high_remainder_bounds {m k : ℕ} {s x : ℤ}
    (hs0 : 0 ≤ s) (hs1 : s < (2 : ℤ) ^ m) :
    0 ≤ s + (2 : ℤ) ^ m * (x % (2 : ℤ) ^ k) ∧
      s + (2 : ℤ) ^ m * (x % (2 : ℤ) ^ k) < (2 : ℤ) ^ (m + k) := by
  have hx0 : 0 ≤ x % (2 : ℤ) ^ k := Int.emod_nonneg _ (two_pow_ne_zero k)
  have hx1 : x % (2 : ℤ) ^ k < (2 : ℤ) ^ k := Int.emod_lt_of_pos _ (two_pow_pos k)
  constructor
  · nlinarith [hs0, two_pow_pos m, hx0]
  · have hle : 1 + x % (2 : ℤ) ^ k ≤ (2 : ℤ) ^ k := by linarith [hx1]
    have hmul : (2 : ℤ) ^ m * (1 + x % (2 : ℤ) ^ k)
        ≤ (2 : ℤ) ^ m * (2 : ℤ) ^ k :=
      mul_le_mul_of_nonneg_left hle (le_of_lt (two_pow_pos m))
    apply lt_of_lt_of_le
    · have : s + (2 : ℤ) ^ m * (x % (2 : ℤ) ^ k)
          < (2 : ℤ) ^ m * (1 + x % (2 : ℤ) ^ k) := by
        have hlt : s + (2 : ℤ) ^ m * (x % (2 : ℤ) ^ k)
            < (2 : ℤ) ^ m + (2 : ℤ) ^ m * (x % (2 : ℤ) ^ k) := by
          linarith [hs1]
        convert hlt using 1
        ring
      exact this
    · exact hmul.trans (le_of_eq (pow_add _ _ _).symm)

private lemma emod_lift_high {m k : ℕ} {s x : ℤ}
    (hs0 : 0 ≤ s) (hs1 : s < (2 : ℤ) ^ m) :
    lift m s x % (2 : ℤ) ^ (m + k) = s + (2 : ℤ) ^ m * (x % (2 : ℤ) ^ k) := by
  have hpow := two_pow_pos (m + k)
  have hdecomp := lift_high_decomp (m := m) (k := k) (s := s) (x := x)
  obtain ⟨hr0, hr1⟩ := lift_high_remainder_bounds (m := m) (k := k) (s := s) (x := x) hs0 hs1
  exact ((Int.ediv_emod_unique (a := lift m s x) (b := (2 : ℤ) ^ (m + k))
      (r := s + (2 : ℤ) ^ m * (x % (2 : ℤ) ^ k))
      (q := x / (2 : ℤ) ^ k) hpow).mpr
    ⟨hdecomp.symm, hr0, hr1⟩).2

private lemma bitOne_lift_high {m k : ℕ} {s x : ℤ}
    (hs0 : 0 ≤ s) (hs1 : s < (2 : ℤ) ^ m) :
    bitOne (lift m s x) (m + k) ↔ bitOne x k := by
  have hpow := two_pow_pos (m + k)
  have hdecomp := lift_high_decomp (m := m) (k := k) (s := s) (x := x)
  obtain ⟨hr0, hr1⟩ := lift_high_remainder_bounds (m := m) (k := k) (s := s) (x := x) hs0 hs1
  have hquot : lift m s x / (2 : ℤ) ^ (m + k) = x / (2 : ℤ) ^ k :=
    ((Int.ediv_emod_unique (a := lift m s x) (b := (2 : ℤ) ^ (m + k))
        (r := s + (2 : ℤ) ^ m * (x % (2 : ℤ) ^ k))
        (q := x / (2 : ℤ) ^ k) hpow).mpr
      ⟨hdecomp.symm, hr0, hr1⟩).1
  simp [bitOne, hquot]

private lemma pv_diff_lt_m {m : ℕ} {s t : ℤ}
    (hs0 : 0 ≤ s) (hs1 : s < (2 : ℤ) ^ m)
    (ht0 : 0 ≤ t) (ht1 : t < (2 : ℤ) ^ m)
    (hne : s ≠ t) : padicValInt 2 (t - s) < m := by
  haveI := instPrimeTwo
  by_contra h
  have hle : m ≤ padicValInt 2 (t - s) := Nat.le_of_not_gt h
  have hne' : t - s ≠ 0 := sub_ne_zero.mpr hne.symm
  have hdvd : (2 : ℤ) ^ m ∣ (t - s) :=
    (padicValInt_dvd_iff (p := 2) m (t - s)).mpr (Or.inr hle)
  obtain ⟨q, hq⟩ := hdvd
  have habs : |t - s| < (2 : ℤ) ^ m := by
    rw [abs_lt]
    constructor <;> linarith
  have habs' : |(2 : ℤ) ^ m * q| < (2 : ℤ) ^ m := by rwa [← hq]
  have hpowpos := two_pow_pos m
  have hqlt : |q| < 1 := by
    have hmul : (2 : ℤ) ^ m * |q| < (2 : ℤ) ^ m := by
      have h' := habs'
      rw [abs_mul, abs_of_pos hpowpos] at h'
      exact h'
    have : |q| * (2 : ℤ) ^ m < (2 : ℤ) ^ m := by rwa [mul_comm] at hmul
    exact (mul_lt_iff_lt_one_left hpowpos).mp this
  have hq0 : q = 0 := by
    have : (q.natAbs : ℤ) < 1 := by
      rwa [Int.abs_eq_natAbs] at hqlt
    have : q.natAbs < 1 := Int.ofNat_lt.mp this
    exact Int.natAbs_eq_zero.mp (Nat.lt_one_iff.mp this)
  exact hne' (by simp [hq0] at hq; exact hq)

private lemma pv_add_pow {m : ℕ} {s t d : ℤ}
    (hs0 : 0 ≤ s) (hs1 : s < (2 : ℤ) ^ m)
    (ht0 : 0 ≤ t) (ht1 : t < (2 : ℤ) ^ m)
    (hne : s ≠ t)
    (hsum : t - s + (2 : ℤ) ^ m * d ≠ 0) :
    padicValInt 2 (t - s + (2 : ℤ) ^ m * d) = padicValInt 2 (t - s) := by
  haveI := instPrimeTwo
  have hst : t - s ≠ 0 := sub_ne_zero.mpr hne.symm
  by_cases hd : d = 0
  · subst hd
    simp
  · have hlt : padicValInt 2 (t - s) < padicValInt 2 ((2 : ℤ) ^ m * d) := by
      have h1 := pv_diff_lt_m hs0 hs1 ht0 ht1 hne
      have h2 := pv2_pow_mul (m := m) hd
      omega
    have hqr : ((t - s : ℤ) : ℚ) + (((2 : ℤ) ^ m * d : ℤ) : ℚ) ≠ 0 := by
      exact_mod_cast hsum
    have hq : ((t - s : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hst
    have hr : (((2 : ℤ) ^ m * d : ℤ) : ℚ) ≠ 0 := by
      exact_mod_cast (mul_ne_zero (two_pow_ne_zero m) hd)
    have hval : padicValRat 2 ((t - s : ℤ) : ℚ)
        < padicValRat 2 (((2 : ℤ) ^ m * d : ℤ) : ℚ) := by
      rw [padicValRat.of_int, padicValRat.of_int]
      exact Int.ofNat_lt.mpr hlt
    have hadd := padicValRat.add_eq_of_lt (p := 2) hqr hq hr hval
    have hsum' : ((t - s : ℤ) : ℚ) + (((2 : ℤ) ^ m * d : ℤ) : ℚ)
        = ((t - s + (2 : ℤ) ^ m * d : ℤ) : ℚ) := by
      norm_cast
    rw [hsum'] at hadd
    rw [padicValRat.of_int, padicValRat.of_int] at hadd
    exact_mod_cast hadd

private lemma pv_lift_same {m : ℕ} {s x y : ℤ} (hxy : x ≠ y) :
    padicValInt 2 (lift m s y - lift m s x) = m + padicValInt 2 (y - x) := by
  have hdiff : lift m s y - lift m s x = (2 : ℤ) ^ m * (y - x) := by
    simp [lift]
    ring
  rw [hdiff, pv2_pow_mul (sub_ne_zero.mpr hxy.symm)]

private lemma pv_lift_diff_res {m : ℕ} {s t x y : ℤ}
    (hs0 : 0 ≤ s) (hs1 : s < (2 : ℤ) ^ m)
    (ht0 : 0 ≤ t) (ht1 : t < (2 : ℤ) ^ m)
    (hne : s ≠ t) :
    padicValInt 2 (lift m t y - lift m s x) = padicValInt 2 (t - s) ∧
      padicValInt 2 (t - s) < m := by
  have hdiff := lift_sub (m := m) (s := s) (t := t) (x := x) (y := y)
  have hne_lift : lift m s x ≠ lift m t y := by
    intro heq
    exact hne (lift_inj hs0 hs1 ht0 ht1 heq).1
  have hsumne : t - s + (2 : ℤ) ^ m * (y - x) ≠ 0 := by
    rw [← hdiff]
    exact sub_ne_zero.mpr hne_lift.symm
  refine ⟨?_, pv_diff_lt_m hs0 hs1 ht0 ht1 hne⟩
  rw [hdiff, pv_add_pow hs0 hs1 ht0 ht1 hne hsumne]

private lemma pairwise_idxOf {r : ℤ → ℤ → Prop} {L : List ℤ} {a b : ℤ}
    (hp : L.Pairwise r) (ha : a ∈ L) (hb : b ∈ L)
    (h : L.idxOf a < L.idxOf b) : r a b := by
  have ha_lt : L.idxOf a < L.length := List.idxOf_lt_length_of_mem ha
  have hb_lt : L.idxOf b < L.length := List.idxOf_lt_length_of_mem hb
  have hae : L.get ⟨L.idxOf a, ha_lt⟩ = a := List.idxOf_get ha_lt
  have hbe : L.get ⟨L.idxOf b, hb_lt⟩ = b := List.idxOf_get hb_lt
  have := (List.pairwise_iff_get.mp hp) ⟨L.idxOf a, ha_lt⟩ ⟨L.idxOf b, hb_lt⟩ h
  simpa [hae, hbe] using this

private lemma idxOf_flatten {L : List (List ℤ)} {a : ℤ} {i : ℕ}
    (hi : i < L.length) (ha : a ∈ L[i])
    (hprev : ∀ j (hj : j < i), a ∉ L[j]'(Nat.lt_trans hj hi)) :
    L.flatten.idxOf a = (L.take i).flatten.length + L[i].idxOf a := by
  induction L generalizing i with
  | nil =>
    cases hi
  | cons l ls ih =>
    cases i with
    | zero =>
      simp [List.flatten_cons]
      exact List.idxOf_append_of_mem (by simpa using ha)
    | succ i =>
      have hnot : a ∉ l := by
        have := hprev 0 (Nat.succ_pos _)
        simpa using this
      have hi' : i < ls.length := by
        simpa using hi
      have ha' : a ∈ ls[i] := by
        simpa using ha
      have hprev' : ∀ j (hj : j < i), a ∉ ls[j]'(Nat.lt_trans hj hi') := by
        intro j hj
        have := hprev (j + 1) (Nat.succ_lt_succ hj)
        simpa using this
      have ih' := ih hi' ha' hprev'
      rw [List.flatten_cons, List.idxOf_append_of_notMem hnot, ih']
      simp [List.take_succ_cons, List.flatten_cons]
      omega


private lemma residues_nodup {m : ℕ} {residues : List ℤ}
    (hres : residues.Perm ((List.range (2 ^ m)).map (fun n : ℕ => (n : ℤ)))) :
    residues.Nodup := by
  have hmap : ((List.range (2 ^ m)).map (fun n : ℕ => (n : ℤ))).Nodup :=
    (List.nodup_map_iff (f := fun n : ℕ => (n : ℤ)) Nat.cast_injective).mpr (List.nodup_range (n := 2 ^ m))
  exact (List.Perm.nodup_iff hres).mpr hmap

private lemma res_in_range {m : ℕ} {residues : List ℤ}
    (hres : residues.Perm ((List.range (2 ^ m)).map (fun n : ℕ => (n : ℤ))))
    {s : ℤ} (hs : s ∈ residues) :
    0 ≤ s ∧ s < (2 : ℤ) ^ m := by
  have hmem : s ∈ (List.range (2 ^ m)).map (fun n : ℕ => (n : ℤ)) :=
    (List.Perm.mem_iff hres).mp hs
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hmem
  have hn' : n < 2 ^ m := List.mem_range.mp hn
  constructor
  · exact Int.natCast_nonneg n
  · have : ((n : ℤ) < ((2 ^ m : ℕ) : ℤ)) := Int.ofNat_lt.mpr hn'
    simpa [Int.natCast_pow] using this

private lemma mem_residues_of_range {m : ℕ} {residues : List ℤ}
    (hres : residues.Perm ((List.range (2 ^ m)).map (fun n : ℕ => (n : ℤ))))
    {s : ℤ} (hs0 : 0 ≤ s) (hs1 : s < (2 : ℤ) ^ m) : s ∈ residues := by
  have hs' : (s.toNat : ℤ) = s := Int.toNat_of_nonneg hs0
  have hn : s.toNat < 2 ^ m := by
    have : (s.toNat : ℤ) < (2 : ℤ) ^ m := by rwa [hs']
    have hpow : (2 : ℤ) ^ m = ((2 ^ m : ℕ) : ℤ) := (Int.natCast_pow 2 m).symm
    rw [hpow] at this
    exact Int.ofNat_lt.mp this
  have hmem : (s.toNat : ℤ) ∈ (List.range (2 ^ m)).map (fun n : ℕ => (n : ℤ)) :=
    List.mem_map.mpr ⟨s.toNat, List.mem_range.mpr hn, rfl⟩
  rw [hs'] at hmem
  exact (List.Perm.mem_iff hres).mpr hmem

private lemma mem_compose (m : ℕ) (A : ℤ → List ℤ) (residues : List ℤ) (z : ℤ) :
    z ∈ composeWord m A residues ↔ ∃ s ∈ residues, ∃ x ∈ A s, z = lift m s x := by
  simp [composeWord, liftBlock, List.mem_flatten, List.mem_map, eq_comm]

private lemma compose_eq {m : ℕ} {A : ℤ → List ℤ} {residues Q : List ℤ}
    (hQ : Q = (residues.map (fun s => (A s).map (fun x => s + (2 : ℤ) ^ m * x))).flatten) :
    Q = composeWord m A residues := by
  simp only [composeWord, liftBlock, lift]
  exact hQ

private lemma idxOf_map_lift {m : ℕ} {s : ℤ} {l : List ℤ} {x : ℤ} (hx : x ∈ l) :
    (l.map (fun y => lift m s y)).idxOf (lift m s x) = l.idxOf x := by
  induction l with
  | nil => cases hx
  | cons b bs ih =>
    by_cases hba : b = x
    · subst hba
      simp
    · have hne : lift m s b ≠ lift m s x := fun h => hba (lift_inj_same h)
      have hx' : x ∈ bs := (List.mem_cons.mp hx).resolve_left (Ne.symm hba)
      simp [List.idxOf_cons, hba, hne, ih hx']

private lemma idxOf_compose {m : ℕ} {A : ℤ → List ℤ} {residues : List ℤ} {s x : ℤ}
    (hres : residues.Perm ((List.range (2 ^ m)).map (fun n : ℕ => (n : ℤ))))
    (hs : s ∈ residues) (hx : x ∈ A s) :
    (composeWord m A residues).idxOf (lift m s x) =
      ((residues.take (residues.idxOf s)).map (liftBlock m A)).flatten.length
        + (A s).idxOf x := by
  set L := residues.map (liftBlock m A)
  set i := residues.idxOf s
  have hi : i < residues.length := List.idxOf_lt_length_of_mem hs
  have hiL : i < L.length := by simp [L, i, hi]
  have hsi : residues[i] = s := List.getElem_idxOf hi
  have hblock : L[i] = liftBlock m A s := by
    simp [L, List.getElem_map, hsi]
  have ha : lift m s x ∈ L[i] := by
    rw [hblock]
    exact List.mem_map.mpr ⟨x, hx, rfl⟩
  have hnd := residues_nodup hres
  have hprev : ∀ j (hj : j < i), lift m s x ∉ L[j]'(Nat.lt_trans hj hiL) := by
    intro j hj
    have hj' : j < residues.length := by
      have hlen : L.length = residues.length := by simp [L]
      omega
    have htmem : residues[j] ∈ residues := List.getElem_mem hj'
    have hst : residues[j] ≠ s := by
      intro heq
      have : residues.idxOf residues[j] = j := List.Nodup.idxOf_getElem hnd j hj'
      rw [heq] at this
      omega
    intro hmem
    have hLj : L[j] = liftBlock m A residues[j] := by
      simp [L, List.getElem_map]
    rw [hLj] at hmem
    obtain ⟨y, hy, heq⟩ := List.mem_map.mp hmem
    have hsr := res_in_range hres hs
    have htr := res_in_range hres htmem
    exact hst (lift_inj hsr.1 hsr.2 htr.1 htr.2 heq.symm).1.symm
  have hflat := idxOf_flatten (L := L) hiL ha hprev
  have htake : L.take i = (residues.take i).map (liftBlock m A) := by
    simp [L, List.map_take]
  have hidxb : L[i].idxOf (lift m s x) = (A s).idxOf x := by
    rw [hblock, liftBlock]
    exact idxOf_map_lift hx
  have hcomp : composeWord m A residues = L.flatten := by
    simp [composeWord, L]
  rw [hcomp, hflat, htake, hidxb]

private lemma idxOf_compose_lt_same {m : ℕ} {A : ℤ → List ℤ} {residues : List ℤ} {s x y : ℤ}
    (hres : residues.Perm ((List.range (2 ^ m)).map (fun n : ℕ => (n : ℤ))))
    (hs : s ∈ residues) (hx : x ∈ A s) (hy : y ∈ A s) :
    (composeWord m A residues).idxOf (lift m s x)
      < (composeWord m A residues).idxOf (lift m s y) ↔
        (A s).idxOf x < (A s).idxOf y := by
  rw [idxOf_compose hres hs hx, idxOf_compose hres hs hy]
  omega

private lemma take_map_flatten_succ {m : ℕ} {A : ℤ → List ℤ} {residues : List ℤ} {i : ℕ}
    (hi : i < residues.length) :
    ((residues.take (i + 1)).map (liftBlock m A)).flatten.length =
      ((residues.take i).map (liftBlock m A)).flatten.length + (A residues[i]).length := by
  rw [List.take_succ_eq_append_getElem hi, List.map_append, List.flatten_append]
  simp [liftBlock]

private lemma idxOf_compose_lt_blocks {m : ℕ} {A : ℤ → List ℤ} {residues : List ℤ} {s t x y : ℤ}
    (hres : residues.Perm ((List.range (2 ^ m)).map (fun n : ℕ => (n : ℤ))))
    (hs : s ∈ residues) (ht : t ∈ residues)
    (hst : residues.idxOf s < residues.idxOf t)
    (hx : x ∈ A s) (hy : y ∈ A t) :
    (composeWord m A residues).idxOf (lift m s x)
      < (composeWord m A residues).idxOf (lift m t y) := by
  rw [idxOf_compose hres hs hx, idxOf_compose hres ht hy]
  set i := residues.idxOf s
  set j := residues.idxOf t
  have hi : i < residues.length := List.idxOf_lt_length_of_mem hs
  have hxlt : (A s).idxOf x < (A s).length := List.idxOf_lt_length_of_mem hx
  have hsi : residues[i] = s := List.getElem_idxOf hi
  have hstep : ((residues.take (i + 1)).map (liftBlock m A)).flatten.length =
      ((residues.take i).map (liftBlock m A)).flatten.length + (A s).length := by
    simpa [hsi] using take_map_flatten_succ (A := A) hi
  have hsplit : residues.take j =
      residues.take (i + 1) ++ (residues.drop (i + 1)).take (j - (i + 1)) := by
    have heq : j = (i + 1) + (j - (i + 1)) := by omega
    conv_lhs => rw [heq]
    exact List.take_add
  have hle : ((residues.take (i + 1)).map (liftBlock m A)).flatten.length
      ≤ ((residues.take j).map (liftBlock m A)).flatten.length := by
    rw [hsplit, List.map_append, List.flatten_append, List.length_append]
    omega
  omega

private lemma ne_of_idxOf_lt {L : List ℤ} {a b : ℤ} (h : L.idxOf a < L.idxOf b) : a ≠ b := by
  intro heq
  subst heq
  exact (lt_irrefl _ h)

private lemma idxOf_block_order {m : ℕ} {A : ℤ → List ℤ} {residues : List ℤ} {s t x y : ℤ}
    (hres : residues.Perm ((List.range (2 ^ m)).map (fun n : ℕ => (n : ℤ))))
    (hs : s ∈ residues) (ht : t ∈ residues) (hst : s ≠ t)
    (hx : x ∈ A s) (hy : y ∈ A t) :
    (composeWord m A residues).idxOf (lift m s x)
      < (composeWord m A residues).idxOf (lift m t y) ↔
        residues.idxOf s < residues.idxOf t := by
  constructor
  · intro h
    by_contra hle
    have hcases : residues.idxOf t < residues.idxOf s ∨ residues.idxOf t = residues.idxOf s := by
      omega
    rcases hcases with hlt | heq
    · have h' := idxOf_compose_lt_blocks hres ht hs hlt hy hx
      omega
    · have hi : residues.idxOf s < residues.length := List.idxOf_lt_length_of_mem hs
      have hj : residues.idxOf t < residues.length := List.idxOf_lt_length_of_mem ht
      have : s = t := by
        have hsget : residues[residues.idxOf s] = s := List.getElem_idxOf hi
        have htget : residues[residues.idxOf t] = t := List.getElem_idxOf hj
        have hs? : residues[residues.idxOf s]? = some s := by
          rw [List.getElem?_eq_getElem hi, hsget]
        have ht? : residues[residues.idxOf t]? = some t := by
          rw [List.getElem?_eq_getElem hj, htget]
        have hidx : residues[residues.idxOf s]? = residues[residues.idxOf t]? := by
          rw [heq]
        apply Option.some.inj
        rw [← hs?, ← ht?, hidx]
      exact hst this
  · intro hlt
    exact idxOf_compose_lt_blocks hres hs ht hlt hx hy

private lemma residue_of_two {m : ℕ} {s t u x y z : ℤ}
    (hs0 : 0 ≤ s) (hs1 : s < (2 : ℤ) ^ m)
    (ht0 : 0 ≤ t) (ht1 : t < (2 : ℤ) ^ m)
    (hu0 : 0 ≤ u) (hu1 : u < (2 : ℤ) ^ m)
    (h : lift m u z = 2 * lift m t y - lift m s x) :
    u = (2 * t - s) % (2 : ℤ) ^ m := by
  have hpow := two_pow_pos m
  have hr0 : 0 ≤ (2 * t - s) % (2 : ℤ) ^ m := Int.emod_nonneg _ (two_pow_ne_zero m)
  have hr1 : (2 * t - s) % (2 : ℤ) ^ m < (2 : ℤ) ^ m := Int.emod_lt_of_pos _ hpow
  have : lift m u z =
      lift m ((2 * t - s) % (2 : ℤ) ^ m)
        (2 * y - x + (2 * t - s) / (2 : ℤ) ^ m) := by
    calc
      lift m u z = 2 * lift m t y - lift m s x := h
      _ = (2 * t - s) + (2 : ℤ) ^ m * (2 * y - x) := by
        simp [lift]; ring
      _ = ((2 * t - s) % (2 : ℤ) ^ m + (2 : ℤ) ^ m * ((2 * t - s) / (2 : ℤ) ^ m))
            + (2 : ℤ) ^ m * (2 * y - x) := by
        conv_lhs => rw [emod_ediv_eq (2 * t - s) ((2 : ℤ) ^ m)]
      _ = lift m ((2 * t - s) % (2 : ℤ) ^ m)
            (2 * y - x + (2 * t - s) / (2 : ℤ) ^ m) := by
        simp [lift]; ring
  exact (lift_inj hu0 hu1 hr0 hr1 this).1

private lemma emod_eq_of_dvd_sub {a b m : ℤ} (h : m ∣ a - b) : a % m = b % m := by
  obtain ⟨q, hq⟩ := h
  have : a = b + m * q := (sub_eq_iff_eq_add').mp hq
  rw [this, Int.add_mul_emod_self_left]

private lemma no_three_AP_residue {θ0 : ℕ → ℤ → Bool} {m : ℕ} {s t u : ℤ}
    (hs0 : 0 ≤ s) (hs1 : s < (2 : ℤ) ^ m)
    (ht0 : 0 ≤ t) (ht1 : t < (2 : ℤ) ^ m)
    (hu0 : 0 ≤ u) (hu1 : u < (2 : ℤ) ^ m)
    (hst : s ≠ t) (htu : t ≠ u)
    (hu : u = (2 * t - s) % (2 : ℤ) ^ m)
    (h1 : treeLt θ0 s t) (h2 : treeLt θ0 t u) : False := by
  haveI := instPrimeTwo
  have hklt : padicValInt 2 (t - s) < m := pv_diff_lt_m hs0 hs1 ht0 ht1 hst
  set k := padicValInt 2 (t - s)
  have hq : 2 * t - s = u + (2 : ℤ) ^ m * ((2 * t - s) / (2 : ℤ) ^ m) := by
    conv_lhs => rw [emod_ediv_eq (2 * t - s) ((2 : ℤ) ^ m)]
    rw [hu]
  have hdiffut : u - t = t - s + (2 : ℤ) ^ m * (-((2 * t - s) / (2 : ℤ) ^ m)) := by
    have := hq
    linarith
  have hune_t : u ≠ t := htu.symm
  have hsumne : t - s + (2 : ℤ) ^ m * (-((2 * t - s) / (2 : ℤ) ^ m)) ≠ 0 := by
    rw [← hdiffut]
    exact sub_ne_zero.mpr hune_t
  have hpvut : padicValInt 2 (u - t) = k := by
    rw [hdiffut, pv_add_pow hs0 hs1 ht0 ht1 hst hsumne]
  have hdvd_st : (2 : ℤ) ^ k ∣ t - s := padicValInt_dvd (p := 2) (t - s)
  have hst_mod : s % (2 : ℤ) ^ k = t % (2 : ℤ) ^ k := by
    refine emod_eq_of_dvd_sub ?_
    have : s - t = -(t - s) := by ring
    rw [this]
    exact dvd_neg.mpr hdvd_st
  have hu_mod : u % (2 : ℤ) ^ k = s % (2 : ℤ) ^ k := by
    have h1' : u % (2 : ℤ) ^ k = (2 * t - s) % (2 : ℤ) ^ k := by
      rw [hu]
      exact emod_pow_of_le (Nat.le_of_lt hklt)
    have h2' : (2 * t - s) % (2 : ℤ) ^ k = s % (2 : ℤ) ^ k := by
      have hring : 2 * t - s = s + 2 * (t - s) := by ring
      rw [hring]
      refine emod_eq_of_dvd_sub ?_
      have : (2 : ℤ) ^ k ∣ 2 * (t - s) := dvd_mul_of_dvd_right hdvd_st 2
      simpa
    exact h1'.trans h2'
  have hflip_st : bitOne t k ↔ ¬ bitOne s k := bitOne_flip (x := s) (y := t) hst
  have hflip_tu : bitOne u k ↔ ¬ bitOne t k := by
    have : padicValInt 2 (u - t) = k := hpvut
    rw [← this]
    exact bitOne_flip (x := t) (y := u) htu
  have hk1 : padicValInt 2 (t - s) = k := rfl
  have hθ1 : bitOne s k ↔ θ0 k (s % (2 : ℤ) ^ k) = true := by
    have := h1.2
    simpa [hk1] using this
  have hθ2 : bitOne t k ↔ θ0 k (t % (2 : ℤ) ^ k) = true := by
    have := h2.2
    simpa [hpvut] using this

  have hsame : bitOne t k ↔ bitOne s k := by
    calc
      bitOne t k ↔ θ0 k (t % (2 : ℤ) ^ k) = true := hθ2
      _ ↔ θ0 k (s % (2 : ℤ) ^ k) = true := by rw [← hst_mod]
      _ ↔ bitOne s k := hθ1.symm
  by_cases hsbit : bitOne s k
  · exact (hflip_st.mp (hsame.mpr hsbit)) hsbit
  · have htbit : ¬ bitOne t k := fun h => hsbit (hsame.mp h)
    have : bitOne t k := (hflip_st.mpr hsbit)
    exact htbit this


private lemma composition_forward (m : ℕ) (A : ℤ → List ℤ) (residues Q : List ℤ)
    (hres : residues.Perm ((List.range (2 ^ m)).map (fun n : ℕ => (n : ℤ))))
    (hQeq : Q = composeWord m A residues)
    (hQsafe : ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) Q) :
    ∀ s : ℤ, 0 ≤ s → s < (2 : ℤ) ^ m → ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) (A s) := by
  intro s hs0 hs1
  have hs : s ∈ residues := mem_residues_of_range hres hs0 hs1
  rw [exists_treeLt_safe_iff] at hQsafe ⊢
  obtain ⟨hcont, hconf⟩ := hQsafe
  refine ⟨?hcontA, ?hconfA⟩
  · intro a b ha hb hmid hord1 hord2
    have haQ : lift m s a ∈ Q := by
      rw [hQeq, mem_compose]
      exact ⟨s, hs, a, ha, rfl⟩
    have hbQ : lift m s b ∈ Q := by
      rw [hQeq, mem_compose]
      exact ⟨s, hs, b, hb, rfl⟩
    have hmidQ : 2 * lift m s b - lift m s a ∈ Q := by
      rw [← lift_two, hQeq, mem_compose]
      exact ⟨s, hs, 2 * b - a, hmid, rfl⟩
    have hord1Q : Q.idxOf (lift m s a) < Q.idxOf (lift m s b) := by
      rw [hQeq]
      exact (idxOf_compose_lt_same hres hs ha hb).mpr hord1
    have hord2Q : Q.idxOf (lift m s b) < Q.idxOf (2 * lift m s b - lift m s a) := by
      rw [hQeq, ← lift_two]
      exact (idxOf_compose_lt_same hres hs hb hmid).mpr hord2
    obtain ⟨hfourth, hord3⟩ := hcont (lift m s a) (lift m s b) haQ hbQ hmidQ hord1Q hord2Q
    have hfourth' : lift m s (3 * b - 2 * a) ∈ composeWord m A residues := by
      rw [lift_three, ← hQeq]
      exact hfourth
    obtain ⟨s', hs', x', hx', heq⟩ := (mem_compose m A residues _).mp hfourth'
    have hsrg := res_in_range hres hs
    have hsrg' := res_in_range hres hs'
    obtain ⟨rfl, rfl⟩ := lift_inj hsrg.1 hsrg.2 hsrg'.1 hsrg'.2 heq
    refine ⟨hx', ?_⟩
    have hord3' : Q.idxOf (lift m s (3 * b - 2 * a)) < Q.idxOf (lift m s (2 * b - a)) := by
      rw [lift_three, lift_two]
      exact hord3
    rw [hQeq] at hord3'
    exact (idxOf_compose_lt_same hres hs hx' hmid).mp hord3'
  · intro a b a' b' ha hb hord hopen2 hopen3 ha' hb' hord' hopen2' hopen3' hpv hmod
    have hab : a ≠ b := ne_of_idxOf_lt hord
    have hab' : a' ≠ b' := ne_of_idxOf_lt hord'
    have haQ : lift m s a ∈ Q := by
      rw [hQeq, mem_compose]; exact ⟨s, hs, a, ha, rfl⟩
    have hbQ : lift m s b ∈ Q := by
      rw [hQeq, mem_compose]; exact ⟨s, hs, b, hb, rfl⟩
    have haQ' : lift m s a' ∈ Q := by
      rw [hQeq, mem_compose]; exact ⟨s, hs, a', ha', rfl⟩
    have hbQ' : lift m s b' ∈ Q := by
      rw [hQeq, mem_compose]; exact ⟨s, hs, b', hb', rfl⟩
    have hordQ : Q.idxOf (lift m s a) < Q.idxOf (lift m s b) := by
      rw [hQeq]; exact (idxOf_compose_lt_same hres hs ha hb).mpr hord
    have hordQ' : Q.idxOf (lift m s a') < Q.idxOf (lift m s b') := by
      rw [hQeq]; exact (idxOf_compose_lt_same hres hs ha' hb').mpr hord'
    have hopen2Q : 2 * lift m s b - lift m s a ∉ Q := by
      intro hmem
      rw [← lift_two, hQeq] at hmem
      obtain ⟨s', hs', x', hx', heq⟩ := (mem_compose m A residues _).mp hmem
      have hsrg := res_in_range hres hs
      have hsrg' := res_in_range hres hs'
      obtain ⟨rfl, rfl⟩ := lift_inj hsrg.1 hsrg.2 hsrg'.1 hsrg'.2 heq
      exact hopen2 hx'
    have hopen3Q : 3 * lift m s b - 2 * lift m s a ∉ Q := by
      intro hmem
      rw [← lift_three, hQeq] at hmem
      obtain ⟨s', hs', x', hx', heq⟩ := (mem_compose m A residues _).mp hmem
      have hsrg := res_in_range hres hs
      have hsrg' := res_in_range hres hs'
      obtain ⟨rfl, rfl⟩ := lift_inj hsrg.1 hsrg.2 hsrg'.1 hsrg'.2 heq
      exact hopen3 hx'
    have hopen2Q' : 2 * lift m s b' - lift m s a' ∉ Q := by
      intro hmem
      rw [← lift_two, hQeq] at hmem
      obtain ⟨s', hs', x', hx', heq⟩ := (mem_compose m A residues _).mp hmem
      have hsrg := res_in_range hres hs
      have hsrg' := res_in_range hres hs'
      obtain ⟨rfl, rfl⟩ := lift_inj hsrg.1 hsrg.2 hsrg'.1 hsrg'.2 heq
      exact hopen2' hx'
    have hopen3Q' : 3 * lift m s b' - 2 * lift m s a' ∉ Q := by
      intro hmem
      rw [← lift_three, hQeq] at hmem
      obtain ⟨s', hs', x', hx', heq⟩ := (mem_compose m A residues _).mp hmem
      have hsrg := res_in_range hres hs
      have hsrg' := res_in_range hres hs'
      obtain ⟨rfl, rfl⟩ := lift_inj hsrg.1 hsrg.2 hsrg'.1 hsrg'.2 heq
      exact hopen3' hx'
    have hpvQ : padicValInt 2 (lift m s b - lift m s a)
        = padicValInt 2 (lift m s b' - lift m s a') := by
      rw [pv_lift_same hab, pv_lift_same hab', hpv]
    have hmodQ : lift m s a % (2 : ℤ) ^ padicValInt 2 (lift m s b - lift m s a)
        = lift m s a' % (2 : ℤ) ^ padicValInt 2 (lift m s b - lift m s a) := by
      rw [pv_lift_same hab, emod_lift_high hs0 hs1, emod_lift_high hs0 hs1, hmod]
    have hbit := hconf (lift m s a) (lift m s b) (lift m s a') (lift m s b')
      haQ hbQ hordQ hopen2Q hopen3Q haQ' hbQ' hordQ' hopen2Q' hopen3Q' hpvQ hmodQ
    have hbit' : bitOne (lift m s b) (m + padicValInt 2 (b - a)) ↔
        bitOne (lift m s b') (m + padicValInt 2 (b - a)) := by
      simpa [pv_lift_same hab] using hbit
    simpa [bitOne_lift_high hs0 hs1, hpv] using hbit'


private lemma composition_backward (m : ℕ) (A : ℤ → List ℤ) (residues Q : List ℤ)
    (hres : residues.Perm ((List.range (2 ^ m)).map (fun n : ℕ => (n : ℤ))))
    (hord : ∃ θ0 : ℕ → ℤ → Bool, residues.Pairwise (treeLt θ0))
    (hQeq : Q = composeWord m A residues)
    (hAs : ∀ s : ℤ, 0 ≤ s → s < (2 : ℤ) ^ m → ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) (A s)) :
    ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) Q := by
  rw [exists_treeLt_safe_iff]
  obtain ⟨θ0, hpair⟩ := hord
  refine ⟨?hcontQ, ?hconfQ⟩
  · intro a b ha hb hmid hord1 hord2
    rw [hQeq] at ha hb hmid
    obtain ⟨s, hs, x, hx, rfl⟩ := (mem_compose m A residues a).mp ha
    obtain ⟨t, ht, y, hy, rfl⟩ := (mem_compose m A residues b).mp hb
    obtain ⟨u, hu, z, hz, hcu⟩ := (mem_compose m A residues (2 * lift m t y - lift m s x)).mp hmid
    have hsrg := res_in_range hres hs
    have htrg := res_in_range hres ht
    have hurg := res_in_range hres hu
    by_cases hst : s = t
    · subst hst
      have heq : lift m s (2 * y - x) = lift m u z := by
        rw [lift_two, hcu]
      obtain ⟨rfl, rfl⟩ := lift_inj hsrg.1 hsrg.2 hurg.1 hurg.2 heq
      have hordA1 : (A s).idxOf x < (A s).idxOf y := by
        have := hord1
        rw [hQeq] at this
        exact (idxOf_compose_lt_same hres hs hx hy).mp this
      have hordA2 : (A s).idxOf y < (A s).idxOf (2 * y - x) := by
        have := hord2
        rw [hQeq, ← lift_two] at this
        exact (idxOf_compose_lt_same hres hs hy hz).mp this
      have hsafeAs : ∃ θ, Safe (treeLt θ) (A s) := hAs s hsrg.1 hsrg.2
      rw [exists_treeLt_safe_iff] at hsafeAs
      obtain ⟨hfourth, hordA3⟩ := hsafeAs.1 x y hx hy hz hordA1 hordA2
      have hfourthQ : 3 * lift m s y - 2 * lift m s x ∈ Q := by
        rw [← lift_three, hQeq, mem_compose]
        exact ⟨s, hs, 3 * y - 2 * x, hfourth, rfl⟩
      refine ⟨hfourthQ, ?_⟩
      have : Q.idxOf (lift m s (3 * y - 2 * x)) < Q.idxOf (lift m s (2 * y - x)) := by
        rw [hQeq]
        exact (idxOf_compose_lt_same hres hs hfourth hz).mpr hordA3
      rwa [lift_three, lift_two] at this
    · have hu_eq : u = (2 * t - s) % (2 : ℤ) ^ m :=
        residue_of_two hsrg.1 hsrg.2 htrg.1 htrg.2 hurg.1 hurg.2 hcu.symm
      have hut : u ≠ t := by
        intro h
        have htmod : t % (2 : ℤ) ^ m = t := Int.emod_eq_of_lt htrg.1 htrg.2
        have : (2 * t - s) % (2 : ℤ) ^ m = t % (2 : ℤ) ^ m := by
          rw [← hu_eq, h, htmod]
        have hsub : (2 * t - s - t) % (2 : ℤ) ^ m = 0 := by
          have := this
          -- (2t-s)% = t% ⇒ ((2t-s)-t)% = 0
          have h' : (2 * t - s - t) % (2 : ℤ) ^ m
              = ((2 * t - s) % (2 : ℤ) ^ m - t % (2 : ℤ) ^ m) % (2 : ℤ) ^ m :=
            Int.sub_emod _ _ _
          rw [h', this, sub_self, Int.zero_emod]
        have : (t - s) % (2 : ℤ) ^ m = 0 := by
          have : 2 * t - s - t = t - s := by ring
          rwa [this] at hsub
        have hdvd : (2 : ℤ) ^ m ∣ t - s := Int.dvd_iff_emod_eq_zero.mpr this
        obtain ⟨q, hq⟩ := hdvd
        have habs : |t - s| < (2 : ℤ) ^ m := by
          rw [abs_lt]; constructor <;> linarith [hsrg.1, hsrg.2, htrg.1, htrg.2]
        have : q = 0 := by
          have habs' : |(2 : ℤ) ^ m * q| < (2 : ℤ) ^ m := by rwa [← hq]
          have hpowpos := two_pow_pos m
          have hmul : (2 : ℤ) ^ m * |q| < (2 : ℤ) ^ m := by
            rwa [abs_mul, abs_of_pos hpowpos] at habs'
          have : |q| * (2 : ℤ) ^ m < (2 : ℤ) ^ m := by rwa [mul_comm] at hmul
          have hqlt : |q| < 1 := (mul_lt_iff_lt_one_left hpowpos).mp this
          have : (q.natAbs : ℤ) < 1 := by rwa [Int.abs_eq_natAbs] at hqlt
          have : q.natAbs < 1 := Int.ofNat_lt.mp this
          exact Int.natAbs_eq_zero.mp (Nat.lt_one_iff.mp this)
        have : t - s = 0 := by simp [this] at hq; exact hq
        exact hst (by omega)
      by_cases hus : u = s
      · have hz' : z ∈ A s := by rwa [hus] at hz
        have hst_idx : residues.idxOf s < residues.idxOf t :=
          (idxOf_block_order hres hs ht hst hx hy).mp (by
            have := hord1
            rwa [hQeq] at this)
        have hts_idx : residues.idxOf t < residues.idxOf s :=
          (idxOf_block_order hres ht hs (Ne.symm hst) hy hz').mp (by
            have := hord2
            rw [hQeq, hcu, hus] at this
            exact this)
        omega
      · have hst_idx : residues.idxOf s < residues.idxOf t :=
          (idxOf_block_order hres hs ht hst hx hy).mp (by
            have := hord1; rwa [hQeq] at this)
        have htu_idx : residues.idxOf t < residues.idxOf u :=
          (idxOf_block_order hres ht hu (Ne.symm hut) hy hz).mp (by
            have := hord2
            rw [hQeq, hcu] at this
            exact this)
        have hstLt : treeLt θ0 s t := pairwise_idxOf hpair hs ht hst_idx
        have htuLt : treeLt θ0 t u := pairwise_idxOf hpair ht hu htu_idx
        exact (no_three_AP_residue hsrg.1 hsrg.2 htrg.1 htrg.2 hurg.1 hurg.2
          hst (Ne.symm hut) hu_eq hstLt htuLt).elim
  · intro a b a' b' ha hb hord1 hopen2 hopen3 ha' hb' hord1' hopen2' hopen3' hpv hmod
    rw [hQeq] at ha hb ha' hb'
    obtain ⟨s, hs, x, hx, rfl⟩ := (mem_compose m A residues a).mp ha
    obtain ⟨t, ht, y, hy, rfl⟩ := (mem_compose m A residues b).mp hb
    obtain ⟨s', hs', x', hx', rfl⟩ := (mem_compose m A residues a').mp ha'
    obtain ⟨t', ht', y', hy', rfl⟩ := (mem_compose m A residues b').mp hb'
    have hsrg := res_in_range hres hs
    have htrg := res_in_range hres ht
    have hsrg' := res_in_range hres hs'
    have htrg' := res_in_range hres ht'
    have hab : lift m s x ≠ lift m t y := ne_of_idxOf_lt (by rwa [hQeq] at hord1)
    have k := padicValInt 2 (lift m t y - lift m s x)
    by_cases hst : s = t
    · -- same residue block: valuation ≥ m, transfer to the child word
      subst hst
      have hxy : x ≠ y := by
        intro hxy
        subst hxy
        exact hab rfl
      have hpv_child : padicValInt 2 (lift m s y - lift m s x) = m + padicValInt 2 (y - x) :=
        pv_lift_same hxy
      have hst' : s' = t' := by
        by_contra hne
        have hinfo := pv_lift_diff_res (x := x') (y := y') hsrg'.1 hsrg'.2 htrg'.1 htrg'.2 hne
        have : padicValInt 2 (lift m t' y' - lift m s' x') = m + padicValInt 2 (y - x) := by
          rw [← hpv_child, hpv]
        have : padicValInt 2 (t' - s') = m + padicValInt 2 (y - x) := by
          rw [← hinfo.1, this]
        omega
      subst hst'
      have hxy' : x' ≠ y' := by
        intro h
        subst h
        have : Q.idxOf (lift m s' x') < Q.idxOf (lift m s' x') := hord1'
        exact (lt_irrefl _ this)
      have hmid_open : 2 * y - x ∉ A s := by
        intro hmem
        have : 2 * lift m s y - lift m s x ∈ Q := by
          rw [← lift_two, hQeq, mem_compose]
          exact ⟨s, hs, 2 * y - x, hmem, rfl⟩
        exact hopen2 this
      have hfourth_open : 3 * y - 2 * x ∉ A s := by
        intro hmem
        have : 3 * lift m s y - 2 * lift m s x ∈ Q := by
          rw [← lift_three, hQeq, mem_compose]
          exact ⟨s, hs, 3 * y - 2 * x, hmem, rfl⟩
        exact hopen3 this
      have hmid_open' : 2 * y' - x' ∉ A s' := by
        intro hmem
        have : 2 * lift m s' y' - lift m s' x' ∈ Q := by
          rw [← lift_two, hQeq, mem_compose]
          exact ⟨s', hs', 2 * y' - x', hmem, rfl⟩
        exact hopen2' this
      have hfourth_open' : 3 * y' - 2 * x' ∉ A s' := by
        intro hmem
        have : 3 * lift m s' y' - 2 * lift m s' x' ∈ Q := by
          rw [← lift_three, hQeq, mem_compose]
          exact ⟨s', hs', 3 * y' - 2 * x', hmem, rfl⟩
        exact hopen3' this
      have hss : s = s' := by
        -- same parent node at level m+k and same residue of a, a' at that level
        -- lift a % 2^{m+k} = s + 2^m (x % 2^k) equals lift a' % = s' + 2^m (x' % 2^k)
        have hmod' : lift m s x % (2 : ℤ) ^ (m + padicValInt 2 (y - x))
            = lift m s' x' % (2 : ℤ) ^ (m + padicValInt 2 (y - x)) := by
          simpa [pv_lift_same hxy] using hmod
        rw [emod_lift_high hsrg.1 hsrg.2, emod_lift_high hsrg'.1 hsrg'.2] at hmod'
        exact (lift_inj hsrg.1 hsrg.2 hsrg'.1 hsrg'.2 hmod').1
      subst hss
      have hsafeAs : ∃ θ, Safe (treeLt θ) (A s) := hAs s hsrg.1 hsrg.2
      rw [exists_treeLt_safe_iff] at hsafeAs
      have hordA : (A s).idxOf x < (A s).idxOf y :=
        (idxOf_compose_lt_same hres hs hx hy).mp (by rwa [hQeq] at hord1)
      have hordA' : (A s).idxOf x' < (A s).idxOf y' :=
        (idxOf_compose_lt_same hres hs hx' hy').mp (by rwa [hQeq] at hord1')
      have hpvA : padicValInt 2 (y - x) = padicValInt 2 (y' - x') := by
        have := hpv
        rw [pv_lift_same hxy, pv_lift_same hxy'] at this
        omega
      have hmodA : x % (2 : ℤ) ^ padicValInt 2 (y - x)
          = x' % (2 : ℤ) ^ padicValInt 2 (y - x) := by
        have hmod' := hmod
        rw [pv_lift_same hxy] at hmod'
        rw [emod_lift_high hsrg.1 hsrg.2, emod_lift_high hsrg.1 hsrg.2] at hmod'
        have := lift_inj_same hmod'
        -- wait, hmod' is equality of two lifts? No, it's equality of remainders
        -- s + 2^m * (x%2^k) = s + 2^m * (x'%2^k)
        have : (2 : ℤ) ^ m * (x % (2 : ℤ) ^ padicValInt 2 (y - x))
            = (2 : ℤ) ^ m * (x' % (2 : ℤ) ^ padicValInt 2 (y - x)) := by
          linarith
        exact mul_left_cancel₀ (two_pow_ne_zero m) this
      have hbitA := hsafeAs.2 x y x' y' hx hy hordA hmid_open hfourth_open
        hx' hy' hordA' hmid_open' hfourth_open' hpvA hmodA
      have : bitOne (lift m s y) (padicValInt 2 (lift m s y - lift m s x)) ↔
          bitOne (lift m s y') (padicValInt 2 (lift m s y - lift m s x)) := by
        rw [pv_lift_same hxy, bitOne_lift_high hsrg.1 hsrg.2,
          bitOne_lift_high hsrg.1 hsrg.2]
        exact hbitA
      exact this
    · -- different residues: k < m, forced bit is the complement of θ0
      have hinfo := pv_lift_diff_res (x := x) (y := y) hsrg.1 hsrg.2 htrg.1 htrg.2 hst
      have hlt := hinfo.2
      have hpvst := hinfo.1
      have hne_st' : s' ≠ t' := by
        intro heq
        subst heq
        have hxy' : lift m s' x' ≠ lift m s' y' := ne_of_idxOf_lt (by rwa [hQeq] at hord1')
        have hxy'' : x' ≠ y' := by
          intro h; subst h; exact hxy' rfl
        have hge : m ≤ padicValInt 2 (lift m s' y' - lift m s' x') := by
          rw [pv_lift_same hxy'']; omega
        rw [← hpv] at hge
        omega
      have hpvst' := (pv_lift_diff_res (x := x') (y := y') hsrg'.1 hsrg'.2 htrg'.1 htrg'.2 hne_st').1
      have hst_idx : residues.idxOf s < residues.idxOf t :=
        (idxOf_block_order hres hs ht hst hx hy).mp (by rwa [hQeq] at hord1)
      have hst_idx' : residues.idxOf s' < residues.idxOf t' :=
        (idxOf_block_order hres hs' ht' hne_st' hx' hy').mp (by rwa [hQeq] at hord1')
      have hθst : treeLt θ0 s t := pairwise_idxOf hpair hs ht hst_idx
      have hθst' : treeLt θ0 s' t' := pairwise_idxOf hpair hs' ht' hst_idx'
      -- both pairs sit at the same residue node
      have hk : padicValInt 2 (t - s) = padicValInt 2 (lift m t y - lift m s x) := hpvst.symm
      have hk' : padicValInt 2 (t' - s') = padicValInt 2 (lift m t y - lift m s x) := by
        rw [← hpvst', hpv]
      have hkk : padicValInt 2 (t - s) = padicValInt 2 (t' - s') := by
        rw [hk, hk']
      have hnode : s % (2 : ℤ) ^ padicValInt 2 (t - s)
          = s' % (2 : ℤ) ^ padicValInt 2 (t - s) := by
        have hmod' := hmod
        rw [hpvst] at hmod'
        have h1 : lift m s x % (2 : ℤ) ^ padicValInt 2 (t - s)
            = s % (2 : ℤ) ^ padicValInt 2 (t - s) :=
          emod_lift_low hsrg.1 hsrg.2 hlt
        have h2 : lift m s' x' % (2 : ℤ) ^ padicValInt 2 (t - s)
            = s' % (2 : ℤ) ^ padicValInt 2 (t - s) :=
          emod_lift_low (k := padicValInt 2 (t - s)) hsrg'.1 hsrg'.2 hlt
        rw [h1, h2] at hmod'
        exact hmod'
      have hbit : bitOne t (padicValInt 2 (t - s)) ↔ bitOne t' (padicValInt 2 (t - s)) := by
        have hflip : bitOne t (padicValInt 2 (t - s)) ↔ ¬ bitOne s (padicValInt 2 (t - s)) :=
          bitOne_flip (x := s) (y := t) hst
        have hflip' : bitOne t' (padicValInt 2 (t' - s')) ↔ ¬ bitOne s' (padicValInt 2 (t' - s')) :=
          bitOne_flip (x := s') (y := t') hne_st'
        have hθ : bitOne s (padicValInt 2 (t - s)) ↔
            θ0 (padicValInt 2 (t - s)) (s % (2 : ℤ) ^ padicValInt 2 (t - s)) = true := hθst.2
        have hθ' : bitOne s' (padicValInt 2 (t' - s')) ↔
            θ0 (padicValInt 2 (t' - s')) (s' % (2 : ℤ) ^ padicValInt 2 (t' - s')) = true := hθst'.2
        have hθeq : θ0 (padicValInt 2 (t - s)) (s % (2 : ℤ) ^ padicValInt 2 (t - s))
            = θ0 (padicValInt 2 (t' - s')) (s' % (2 : ℤ) ^ padicValInt 2 (t' - s')) := by
          rw [hnode, hkk]
        calc
          bitOne t (padicValInt 2 (t - s)) ↔ ¬ bitOne s (padicValInt 2 (t - s)) := hflip
          _ ↔ ¬ (θ0 (padicValInt 2 (t - s)) (s % (2 : ℤ) ^ padicValInt 2 (t - s)) = true) := by
            rw [hθ]
          _ ↔ ¬ (θ0 (padicValInt 2 (t' - s')) (s' % (2 : ℤ) ^ padicValInt 2 (t' - s')) = true) := by
            rw [hθeq]
          _ ↔ ¬ bitOne s' (padicValInt 2 (t' - s')) := by rw [hθ']
          _ ↔ bitOne t' (padicValInt 2 (t' - s')) := hflip'.symm
          _ ↔ bitOne t' (padicValInt 2 (t - s)) := by rw [hkk]
      have : bitOne (lift m t y) (padicValInt 2 (lift m t y - lift m s x)) ↔
          bitOne (lift m t' y') (padicValInt 2 (lift m t y - lift m s x)) := by
        have h1 : bitOne (lift m t y) (padicValInt 2 (lift m t y - lift m s x))
            ↔ bitOne t (padicValInt 2 (t - s)) := by
          rw [hpvst]
          exact bitOne_lift_low htrg.1 htrg.2 hlt
        have h2 : bitOne (lift m t' y') (padicValInt 2 (lift m t y - lift m s x))
            ↔ bitOne t' (padicValInt 2 (t - s)) := by
          rw [← hk]
          exact bitOne_lift_low (k := padicValInt 2 (t - s)) htrg'.1 htrg'.2 hlt
        rw [h1, h2]
        exact hbit
      exact this

theorem safe_word_composition (m : ℕ) (hm : 0 < m) (A : ℤ → List ℤ)
    (residues : List ℤ)
    (hres : residues.Perm ((List.range (2 ^ m)).map (fun n : ℕ => (n : ℤ))))
    (hord : ∃ θ0 : ℕ → ℤ → Bool, residues.Pairwise (treeLt θ0))
    (Q : List ℤ)
    (hQ : Q = (residues.map (fun s => (A s).map (fun x => s + (2 : ℤ) ^ m * x))).flatten) :
    (∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) Q) ↔
      (∀ s : ℤ, 0 ≤ s → s < (2 : ℤ) ^ m → ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) (A s)) := by
  have hQeq : Q = composeWord m A residues := compose_eq hQ
  constructor
  · intro hQsafe
    exact composition_forward m A residues Q hres hQeq hQsafe
  · intro hAs
    exact composition_backward m A residues Q hres hord hQeq hAs

end Erdos195

theorem solution (m : ℕ) (hm : 0 < m) (A : ℤ → List ℤ)
    (residues : List ℤ)
    (hres : residues.Perm ((List.range (2 ^ m)).map (fun n : ℕ => (n : ℤ))))
    (hord : ∃ θ0 : ℕ → ℤ → Bool, residues.Pairwise (Erdos195.treeLt θ0))
    (Q : List ℤ)
    (hQ : Q = (residues.map (fun s => (A s).map (fun x => s + (2 : ℤ) ^ m * x))).flatten) :
    (∃ θ : ℕ → ℤ → Bool, Erdos195.Safe (Erdos195.treeLt θ) Q) ↔
      (∀ s : ℤ, 0 ≤ s → s < (2 : ℤ) ^ m →
        ∃ θ : ℕ → ℤ → Bool, Erdos195.Safe (Erdos195.treeLt θ) (A s)) :=
  Erdos195.safe_word_composition m hm A residues hres hord Q hQ
