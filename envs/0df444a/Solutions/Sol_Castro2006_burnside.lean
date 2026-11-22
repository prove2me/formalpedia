-- Prove2me | solution 1 for Castro2006.burnside
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-22T20:25:39.779996+00:00
-- url     : https://prove2.me/submissions/d7f8d45c-d549-43a4-9401-9698c15bb9ce

import Mathlib
import Theorems.Thm_Castro2006_lema_4_5_2

namespace Castro2006Burnside

open Subgroup

/-- `S m r = 1 + r + ... + r^(m-1)`. -/
def S : ℕ → ℤ → ℤ
  | 0, _ => 0
  | m + 1, r => 1 + r * S m r

lemma S_two_mul (t : ℤ) (m : ℕ) :
    ∃ q : ℤ, 2 * S m (1 + t) = 2 * m + t * m * (m - 1) + t ^ 2 * q := by
  induction m with
  | zero => exact ⟨0, by simp [S]⟩
  | succ m ih =>
    obtain ⟨q, hq⟩ := ih
    refine ⟨m * (m - 1) + q + t * q, ?_⟩
    simp only [S]
    push_cast
    linear_combination (1 + t) * hq

lemma nt_odd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ} (hn : 2 ≤ n) {r s : ℤ}
    (hr : r ≡ 1 [ZMOD p ^ (n - 1)]) (hr1 : ¬ r ≡ 1 [ZMOD p ^ n])
    (hs : (p : ℤ) ^ n ∣ (r - 1) * s) :
    ∃ j : ℤ, (p : ℤ) ^ n ∣ j * S p r + s := by
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
  simp only [show n + 2 - 1 = n + 1 by omega] at hr
  obtain ⟨k, hk⟩ : (p : ℤ) ^ (n + 1) ∣ r - 1 := hr.symm.dvd
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hk' : ¬ (p : ℤ) ∣ k := by
    rintro ⟨l, hl⟩
    apply hr1
    rw [Int.modEq_iff_dvd]
    exact ⟨-l, by linear_combination (-1 : ℤ) * hk - (p : ℤ) ^ (n + 1) * hl⟩
  have hps : (p : ℤ) ∣ s := by
    have h1 : (p : ℤ) ^ (n + 1) * p ∣ (p : ℤ) ^ (n + 1) * (k * s) := by
      have : (r - 1) * s = (p : ℤ) ^ (n + 1) * (k * s) := by rw [hk]; ring
      rw [← this, ← pow_succ]; exact hs
    have h2 := (mul_dvd_mul_iff_left (pow_ne_zero (n + 1) hpZ.ne_zero)).mp h1
    rcases hpZ.dvd_or_dvd h2 with h | h
    · exact absurd h hk'
    · exact h
  obtain ⟨u, rfl⟩ := hps
  refine ⟨-u, ?_⟩
  have hr' : r = 1 + (p : ℤ) ^ (n + 1) * k := by linarith
  obtain ⟨q, hq⟩ := S_two_mul ((p : ℤ) ^ (n + 1) * k) p
  rw [← hr'] at hq
  have hcop : IsCoprime ((p : ℤ) ^ (n + 2)) 2 := by
    have : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr hp2
    have h := Nat.isCoprime_iff_coprime.mpr this
    push_cast at h
    exact h.pow_left
  have h2 : (p : ℤ) ^ (n + 2) ∣ (S p r - p) * 2 := by
    refine ⟨k * (p - 1) + (p : ℤ) ^ n * k ^ 2 * q, ?_⟩
    linear_combination hq
  have h3 := hcop.dvd_of_dvd_mul_right h2
  obtain ⟨c, hc⟩ := h3
  exact ⟨-u * c, by linear_combination (-u) * hc⟩

lemma nt_two {n : ℕ} (hn : 2 ≤ n) {r s : ℤ}
    (hr : r ≡ 1 [ZMOD 2 ^ (n - 1)] ∨ r ≡ -1 [ZMOD 2 ^ (n - 1)])
    (hr1 : ¬ r ≡ 1 [ZMOD 2 ^ n]) (hr2 : ¬ r ≡ -1 [ZMOD 2 ^ n])
    (hs : (2 : ℤ) ^ n ∣ (r - 1) * s) :
    ∃ j : ℤ, (2 : ℤ) ^ n ∣ j * (1 + r) + s := by
  rcases hr with hr | hr
  · obtain ⟨k, hk⟩ : (2 : ℤ) ^ (n - 1) ∣ r - 1 := hr.symm.dvd
    have hkodd : ¬ (2 : ℤ) ∣ k := by
      rintro ⟨l, hl⟩
      apply hr1
      rw [Int.modEq_iff_dvd]
      refine ⟨-l, ?_⟩
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      simp only [Nat.add_sub_cancel] at hk
      linear_combination (-1 : ℤ) * hk - (2 : ℤ) ^ n' * hl
    obtain ⟨l, hl⟩ : ∃ l, k = 2 * l + 1 := ⟨k / 2, by omega⟩
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · exfalso
      obtain rfl : n = 2 := by omega
      apply hr2
      rw [Int.modEq_iff_dvd]
      exact ⟨-(l + 1), by simp at hk; linear_combination (-1 : ℤ) * hk - 2 * hl⟩
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 3 := ⟨n - 3, by omega⟩
    simp only [show n + 3 - 1 = n + 2 by omega] at hk
    have hs2 : (2 : ℤ) ∣ s := by
      have : (r - 1) * s = (2 : ℤ) ^ (n + 2) * (k * s) := by rw [hk]; ring
      rw [this, show n + 3 = (n + 2) + 1 by omega, pow_succ] at hs
      have h2 := (mul_dvd_mul_iff_left (pow_ne_zero (n + 2) (two_ne_zero' ℤ))).mp hs
      rw [hl] at h2
      have : s = (2 * l + 1) * s - 2 * (l * s) := by ring
      rw [this]
      exact dvd_sub h2 (dvd_mul_right _ _)
    obtain ⟨u, rfl⟩ := hs2
    have hr' : r = 1 + 2 ^ (n + 2) * k := by linarith
    refine ⟨-u + u * (k * 2 ^ (n + 1)), u * k ^ 2 * 2 ^ n, ?_⟩
    rw [hr']
    ring
  · obtain ⟨k, hk⟩ : (2 : ℤ) ^ (n - 1) ∣ r - (-1) := hr.symm.dvd
    have hkodd : ¬ (2 : ℤ) ∣ k := by
      rintro ⟨l, hl⟩
      apply hr2
      rw [Int.modEq_iff_dvd]
      refine ⟨-l, ?_⟩
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      simp only [Nat.add_sub_cancel] at hk
      linear_combination (-1 : ℤ) * hk - (2 : ℤ) ^ n' * hl
    obtain ⟨l, hl⟩ : ∃ l, k = 2 * l + 1 := ⟨k / 2, by omega⟩
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · exfalso
      obtain rfl : n = 2 := by omega
      apply hr1
      rw [Int.modEq_iff_dvd]
      exact ⟨-l, by simp at hk; linear_combination (-1 : ℤ) * hk - 2 * hl⟩
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 3 := ⟨n - 3, by omega⟩
    simp only [show n + 3 - 1 = n + 2 by omega] at hk
    have hr' : r = 2 ^ (n + 2) * k - 1 := by linarith
    have hs2 : (2 : ℤ) ^ (n + 2) ∣ s := by
      have : (r - 1) * s = (2 : ℤ) * ((2 * l + 1) * 2 ^ (n + 1) - 1) * s := by
        rw [hr', hl]; ring
      rw [this, show n + 3 = 1 + (n + 2) by omega, pow_add, pow_one, mul_assoc] at hs
      have h2 := (mul_dvd_mul_iff_left (two_ne_zero' ℤ)).mp hs
      have hcop : IsCoprime ((2 : ℤ) ^ (n + 2)) ((2 * l + 1) * 2 ^ (n + 1) - 1) := by
        apply IsCoprime.pow_left
        exact ⟨(2 * l + 1) * 2 ^ n, -1, by ring⟩
      exact hcop.dvd_of_dvd_mul_left h2
    obtain ⟨v, rfl⟩ := hs2
    refine ⟨v, v * (l + 1), ?_⟩
    rw [hr', hl]
    ring

lemma nt_two_neg {n : ℕ} (hn : 1 ≤ n) {r s : ℤ} (hr : r ≡ -1 [ZMOD 2 ^ n])
    (hs : (2 : ℤ) ^ n ∣ (r - 1) * s) (hs0 : ¬ (2 : ℤ) ^ n ∣ s) :
    s ≡ 2 ^ (n - 1) [ZMOD 2 ^ n] := by
  obtain ⟨c, hc⟩ : (2 : ℤ) ^ n ∣ r - (-1) := hr.symm.dvd
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have h1 : (2 : ℤ) ^ (n + 1) ∣ 2 * s := by
    have : 2 * s = (2 : ℤ) ^ (n + 1) * (c * s) - (r - 1) * s := by
      rw [show r = 2 ^ (n + 1) * c - 1 by linarith]; ring
    rw [this]; exact dvd_sub (dvd_mul_right _ _) hs
  rw [pow_succ, mul_comm] at h1
  obtain ⟨v, rfl⟩ := (mul_dvd_mul_iff_left (two_ne_zero' ℤ)).mp h1
  have hv : ¬ (2 : ℤ) ∣ v := by
    rintro ⟨w, rfl⟩; exact hs0 ⟨w, by ring⟩
  obtain ⟨w, hw⟩ : ∃ w, v = 2 * w + 1 := ⟨v / 2, by omega⟩
  rw [Int.modEq_iff_dvd]
  exact ⟨-w, by rw [hw]; ring⟩

lemma first_pow {p : ℕ} {G : Type*} [Group G] (hG : IsPGroup p G) (H : Subgroup G) {x : G}
    (hx : x ∉ H) : ∃ i : ℕ, x ^ p ^ i ∉ H ∧ (x ^ p ^ i) ^ p ∈ H := by
  classical
  obtain ⟨N, hN⟩ := hG x
  have hex : ∃ i, x ^ p ^ i ∈ H := ⟨N, by rw [hN]; exact H.one_mem⟩
  have hi : x ^ p ^ Nat.find hex ∈ H := Nat.find_spec hex
  have hi0 : Nat.find hex ≠ 0 := by
    intro h; rw [h] at hi; exact hx (by simpa using hi)
  obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := ⟨Nat.find hex - 1, by omega⟩
  refine ⟨j, Nat.find_min hex (by omega), ?_⟩
  rw [← pow_mul, ← pow_succ, ← hj]; exact hi

lemma local_step {p : ℕ} (hp : p.Prime) {G : Type*} [Group G] {a : G}
    (hAn : (zpowers a).Normal) {n : ℕ} (ha : orderOf a = p ^ n)
    (hcent : centralizer (zpowers a : Set G) ≤ zpowers a)
    (hkey : ∀ g : G, g ^ p = 1 → g ∈ zpowers a)
    {y : G} (hy : y ∉ zpowers a) (hyp : y ^ p ∈ zpowers a) :
    p = 2 ∧ 2 ≤ n ∧ y * a * y⁻¹ = a⁻¹ ∧ y ^ 2 = a ^ (2 ^ (n - 1)) := by
  have hoa : ((orderOf a : ℕ) : ℤ) = (p : ℤ) ^ n := by rw [ha]; push_cast; rfl
  obtain ⟨r, hr⟩ := mem_zpowers_iff.mp (hAn.conj_mem a (mem_zpowers a) y)
  obtain ⟨s, hs⟩ := mem_zpowers_iff.mp hyp
  have hconj : ∀ k : ℤ, y * a ^ k * y⁻¹ = a ^ (r * k) := by
    intro k; rw [← conj_zpow, ← hr, zpow_mul]
  have hcomm : ∀ k : ℤ, y * a ^ k = a ^ (r * k) * y := by
    intro k; rw [← hconj k]; group
  have hrs : (p : ℤ) ^ n ∣ (r - 1) * s := by
    have h : a ^ s = a ^ (r * s) := by
      rw [← hconj s, hs]; group
    rw [zpow_eq_zpow_iff_modEq, hoa] at h
    have := h.dvd
    rw [show r * s - s = (r - 1) * s by ring] at this
    exact this
  have hpowconj : ∀ m : ℕ, y ^ m * a * (y ^ m)⁻¹ = a ^ (r ^ m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc y ^ (m + 1) * a * (y ^ (m + 1))⁻¹ = y * (y ^ m * a * (y ^ m)⁻¹) * y⁻¹ := by group
        _ = a ^ (r ^ (m + 1)) := by rw [ih, hconj, pow_succ]; ring_nf
  have hrp : r ^ p ≡ 1 [ZMOD p ^ n] := by
    have h : a ^ (r ^ p) = a ^ (1 : ℤ) := by
      rw [← hpowconj p, ← hs, zpow_one]; group
    rw [zpow_eq_zpow_iff_modEq, hoa] at h
    exact h
  have hr1 : ¬ r ≡ 1 [ZMOD p ^ n] := by
    intro h
    apply hy
    apply hcent
    rw [mem_centralizer_iff]
    intro g hg
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
    have har : a ^ r = a := by
      rw [← zpow_one a, ← zpow_mul, one_mul, zpow_eq_zpow_iff_modEq, hoa]; exact h
    have := hcomm k
    rw [zpow_mul, har] at this
    exact this.symm
  have hpow : ∀ j : ℤ, ∀ m : ℕ, (a ^ j * y) ^ m = a ^ (j * S m r) * y ^ m := by
    intro j m
    induction m with
    | zero => simp [S]
    | succ m ih =>
      rw [pow_succ', ih, S]
      calc a ^ j * y * (a ^ (j * S m r) * y ^ m)
          = a ^ j * (y * a ^ (j * S m r)) * y ^ m := by group
        _ = a ^ (j * (1 + r * S m r)) * y ^ (m + 1) := by
          rw [hcomm, ← mul_assoc, ← zpow_add, mul_assoc, ← pow_succ']; ring_nf
  have hno : ∀ j : ℤ, ¬ (p : ℤ) ^ n ∣ j * S p r + s := by
    intro j hj
    apply hy
    have h1 : a ^ (j * S p r + s) = 1 := by
      rw [← orderOf_dvd_iff_zpow_eq_one, hoa]; exact hj
    have h2 : (a ^ j * y) ^ p = 1 := by
      rw [hpow, ← hs, ← zpow_add, h1]
    have h3 := hkey _ h2
    exact (Subgroup.mul_mem_cancel_left _ (zpow_mem (mem_zpowers a) j)).mp h3
  have hn2 : 2 ≤ n := by
    by_contra hlt
    rcases (show n = 0 ∨ n = 1 by omega) with h0 | h1
    · subst h0; exact hr1 (by simp [Int.modEq_one])
    · subst h1
      apply hr1
      haveI := Fact.mk hp
      rw [pow_one] at hrp ⊢
      rw [← ZMod.intCast_eq_intCast_iff] at hrp ⊢
      push_cast at hrp ⊢
      rw [ZMod.pow_card] at hrp
      exact hrp
  obtain ⟨hodd, htwo⟩ := Castro2006.lema_4_5_2 hp r n hn2 hrp hr1
  by_cases hp2 : p = 2
  · subst hp2
    have hS2 : S 2 r = 1 + r := by simp [S]
    by_cases hneg : r ≡ -1 [ZMOD 2 ^ n]
    · have hya : y * a * y⁻¹ = a⁻¹ := by
        rw [← hr, ← zpow_neg_one, zpow_eq_zpow_iff_modEq, hoa]
        push_cast; exact hneg
      have hs0 : ¬ (2 : ℤ) ^ n ∣ s := by
        intro h; apply hno 0; simpa using h
      have hsm := nt_two_neg (by omega) hneg (by exact_mod_cast hrs) hs0
      refine ⟨rfl, hn2, hya, ?_⟩
      rw [← hs, ← zpow_natCast, zpow_eq_zpow_iff_modEq, hoa]
      push_cast
      exact hsm
    · exfalso
      obtain ⟨j, hj⟩ := nt_two hn2 (by exact_mod_cast htwo rfl) (by exact_mod_cast hr1)
        hneg (by exact_mod_cast hrs)
      apply hno j
      rw [hS2]; exact_mod_cast hj
  · exfalso
    obtain ⟨j, hj⟩ := nt_odd hp hp2 hn2 (hodd hp2) hr1 hrs
    exact hno j hj

lemma comm_cyclic {p : ℕ} (hp : p.Prime) {G : Type*} [Group G] [Finite G] (hG : IsPGroup p G)
    (hkey : ∀ H : Subgroup G, H ≠ ⊥ → ∀ g : G, g ^ p = 1 → g ∈ H)
    (B : Subgroup G) (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) :
    ∃ g ∈ B, B = zpowers g := by
  haveI := Fact.mk hp
  obtain ⟨g, hgB, hgmax⟩ := Set.exists_max_image (B : Set G) orderOf (Set.toFinite _)
    ⟨1, B.one_mem⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_orderOf.mp hG g
  have hexp : ∀ h ∈ B, h ^ p ^ m = 1 := by
    intro h hh
    obtain ⟨b, hb⟩ := IsPGroup.iff_orderOf.mp hG h
    have hle := hgmax h hh
    rw [hb, hm, Nat.pow_le_pow_iff_right hp.one_lt] at hle
    rw [← orderOf_dvd_iff_pow_eq_one, hb]
    exact pow_dvd_pow p hle
  refine ⟨g, hgB, le_antisymm ?_ (zpowers_le.mpr hgB)⟩
  intro h hh
  by_contra hn
  obtain ⟨i, hi1, hi2⟩ := first_pow hG _ hn
  set y := h ^ p ^ i with hy
  have hyB : y ∈ B := pow_mem hh _
  obtain ⟨t, ht⟩ := mem_zpowers_iff.mp hi2
  rcases m with _ | m
  · apply hi1
    have := hexp y hyB
    rw [pow_zero, pow_one] at this
    rw [this]; exact one_mem _
  have hpt : (p : ℤ) ∣ t := by
    have h1 : g ^ (t * (p ^ m : ℕ)) = 1 := by
      rw [zpow_mul, ht, zpow_natCast, ← pow_mul, ← pow_succ']
      exact hexp y hyB
    rw [← orderOf_dvd_iff_zpow_eq_one, hm] at h1
    push_cast at h1
    rw [pow_succ'] at h1
    exact (mul_dvd_mul_iff_right (pow_ne_zero m (by exact_mod_cast hp.ne_zero : (p : ℤ) ≠ 0))).mp h1
  obtain ⟨u, rfl⟩ := hpt
  have hz : (y * g ^ (-u)) ^ p = 1 := by
    have hc : Commute y (g ^ (-u)) := hB _ hyB _ (zpow_mem hgB _)
    rw [hc.mul_pow, ← ht, ← zpow_natCast, ← zpow_mul, ← zpow_add]
    ring_nf; simp
  have hne : zpowers g ≠ ⊥ := by
    intro hb
    have : g = 1 := by
      have := mem_zpowers g; rw [hb] at this; exact (mem_bot.mp this)
    rw [this, orderOf_one] at hm
    exact (Nat.one_lt_pow (Nat.succ_ne_zero m) hp.one_lt).ne hm
  have := hkey _ hne _ hz
  exact hi1 ((Subgroup.mul_mem_cancel_right _ (zpow_mem (mem_zpowers g) _)).mp this)

lemma exists_selfcent {p : ℕ} (hp : p.Prime) {G : Type*} [Group G] [Finite G]
    (hG : IsPGroup p G) :
    ∃ A : Subgroup G, A.Normal ∧ (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) ∧
      centralizer (A : Set G) ≤ A := by
  haveI := Fact.mk hp
  let Sset : Set (Subgroup G) := {A | A.Normal ∧ ∀ x ∈ A, ∀ y ∈ A, x * y = y * x}
  obtain ⟨A, hAmax⟩ := Sset.toFinite.exists_maximal ⟨⊥, ⟨inferInstance, by simp⟩⟩
  obtain ⟨⟨hAn, hAc⟩, hmax⟩ := hAmax
  refine ⟨A, hAn, hAc, ?_⟩
  intro c hc
  by_contra hcA
  let mk := QuotientGroup.mk' A
  have hQ : IsPGroup p (G ⧸ A) := hG.to_quotient A
  let N : Subgroup (G ⧸ A) := (centralizer (A : Set G)).map mk
  haveI hNn : N.Normal := Subgroup.Normal.map inferInstance mk (QuotientGroup.mk'_surjective A)
  have hNp : IsPGroup p N := hQ.to_subgroup N
  have hcN : mk c ∈ N := mem_map_of_mem _ hc
  have hc1 : mk c ≠ 1 := by
    rw [ne_eq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact hcA
  have hdvd : p ∣ Nat.card N := by
    haveI : Nontrivial N := ⟨⟨⟨mk c, hcN⟩, 1, fun h => hc1 (congrArg Subtype.val h)⟩⟩
    obtain ⟨k, hk0, hk⟩ := hNp.nontrivial_iff_card.mp inferInstance
    rw [hk]; exact dvd_pow_self _ (ne_of_gt hk0)
  have hCp : IsPGroup p (ConjAct (G ⧸ A)) := hQ.of_equiv ConjAct.toConjAct
  obtain ⟨b, hbfix, hb1⟩ := hCp.exists_fixed_point_of_prime_dvd_card_of_fixed_point N hdvd
    (a := (1 : N)) (by simp [MulAction.mem_fixedPoints])
  have hbc : ∀ q : G ⧸ A, q * (b : G ⧸ A) * q⁻¹ = b := by
    intro q
    have := congrArg Subtype.val (hbfix (ConjAct.toConjAct q))
    rw [ConjAct.Subgroup.val_conj_smul, ConjAct.smul_def] at this
    simpa using this
  obtain ⟨c', hc', hc'b⟩ := mem_map.mp b.2
  let B : Subgroup G := (zpowers (b : G ⧸ A)).comap mk
  have hZn : (zpowers (b : G ⧸ A)).Normal := by
    constructor
    intro x hx q
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
    rw [← conj_zpow, hbc]
    exact zpow_mem (mem_zpowers _) k
  have hBn : B.Normal := hZn.comap mk
  have hform : ∀ x ∈ B, ∃ k : ℤ, ∃ a ∈ A, x = c' ^ k * a := by
    intro x hx
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (mem_comap.mp hx)
    refine ⟨k, (c' ^ k)⁻¹ * x, ?_, by group⟩
    rw [← QuotientGroup.eq]
    have : mk (c' ^ k) = mk x := by rw [map_zpow, hc'b, hk]
    exact this
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    intro x hx y hy
    obtain ⟨k, a1, ha1, rfl⟩ := hform x hx
    obtain ⟨l, a2, ha2, rfl⟩ := hform y hy
    have hu : c' ^ k ∈ centralizer (A : Set G) := zpow_mem hc' k
    have hv : c' ^ l ∈ centralizer (A : Set G) := zpow_mem hc' l
    rw [mem_centralizer_iff] at hu hv
    have e1 : a1 * c' ^ l = c' ^ l * a1 := hv a1 ha1
    have e2 : a2 * c' ^ k = c' ^ k * a2 := hu a2 ha2
    have e3 : c' ^ k * c' ^ l = c' ^ l * c' ^ k := by rw [← zpow_add, ← zpow_add, add_comm]
    have e4 : a1 * a2 = a2 * a1 := hAc a1 ha1 a2 ha2
    calc c' ^ k * a1 * (c' ^ l * a2) = (c' ^ k * c' ^ l) * (a1 * a2) := by
          rw [mul_assoc, ← mul_assoc a1, e1]; group
      _ = (c' ^ l * c' ^ k) * (a2 * a1) := by rw [e3, e4]
      _ = c' ^ l * a2 * (c' ^ k * a1) := by
          rw [mul_assoc, ← mul_assoc (c' ^ k), ← e2]; group
  have hAB : A ≤ B := by
    intro x hx
    rw [mem_comap]
    have : mk x = 1 := by rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact hx
    rw [this]; exact one_mem _
  have hBA := hmax ⟨hBn, hBc⟩ hAB
  have hc'B : c' ∈ B := by rw [mem_comap, hc'b]; exact mem_zpowers _
  have hc'A := hBA hc'B
  apply hb1
  apply Subtype.ext
  rw [← hc'b]
  show (1 : G ⧸ A) = mk c'
  rw [eq_comm, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact hc'A

end Castro2006Burnside

open Castro2006Burnside Subgroup in
theorem solution {p : ℕ} (hp : p.Prime) {G : Type} [Group G] [Fintype G]
    (hG : IsPGroup p G) (hunique : ∃! H : Subgroup G, Nat.card H = p) :
    IsCyclic G ∨ ∃ m : ℕ, 1 ≤ m ∧ Nonempty (G ≃* QuaternionGroup (2 ^ m)) := by
  classical
  haveI := Fact.mk hp
  obtain ⟨P, hP, hPu⟩ := hunique
  have hzp : ∀ g : G, g ≠ 1 → g ^ p = 1 → zpowers g = P := by
    intro g hg1 hgp
    apply hPu
    rw [Nat.card_zpowers, orderOf_eq_prime hgp hg1]
  have hkey : ∀ H : Subgroup G, H ≠ ⊥ → ∀ g : G, g ^ p = 1 → g ∈ H := by
    intro H hH g hgp
    by_cases hg1 : g = 1
    · rw [hg1]; exact one_mem _
    haveI : Nontrivial H := (nontrivial_iff_ne_bot H).mpr hH
    obtain ⟨k, hk0, hk⟩ := (hG.to_subgroup H).nontrivial_iff_card.mp inferInstance
    have hdvd : p ∣ Nat.card H := by rw [hk]; exact dvd_pow_self _ (ne_of_gt hk0)
    obtain ⟨h, hh⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have hh' : orderOf (h : G) = p := by rw [Subgroup.orderOf_coe]; exact hh
    have hh1 : (h : G) ≠ 1 := by
      intro h1; rw [h1, orderOf_one] at hh'; exact hp.one_lt.ne hh'
    have hhp : (h : G) ^ p = 1 := by rw [← hh']; exact pow_orderOf_eq_one _
    have : zpowers g ≤ H := by
      rw [hzp g hg1 hgp, ← hzp _ hh1 hhp, zpowers_le]; exact h.2
    exact this (mem_zpowers g)
  obtain ⟨A, hAn, hAc, hcent⟩ := exists_selfcent hp hG
  obtain ⟨a, -, rfl⟩ := comm_cyclic hp hG hkey A hAc
  obtain ⟨n, ha⟩ := IsPGroup.iff_orderOf.mp hG a
  by_cases hall : ∀ x : G, x ∈ zpowers a
  · left; exact ⟨a, hall⟩
  push_neg at hall
  obtain ⟨x, hx⟩ := hall
  have hne : zpowers a ≠ ⊥ := by
    intro h; apply hx; apply hcent; rw [h]
    rw [mem_centralizer_iff]; intro g hg
    simp at hg; simp [hg]
  have hkeyA := hkey _ hne
  obtain ⟨i, hi1, hi2⟩ := first_pow hG _ hx
  obtain ⟨rfl, hn2, hya, hy2⟩ := local_step hp hAn ha hcent hkeyA hi1 hi2
  set y := x ^ 2 ^ i with hydef
  have hoa : ((orderOf a : ℕ) : ℤ) = (2 : ℤ) ^ n := by rw [ha]; push_cast; rfl
  -- every element outside `⟨a⟩` inverts `a`
  have hinv : ∀ g, g ∉ zpowers a → g * a * g⁻¹ = a⁻¹ := by
    intro g hg
    obtain ⟨j, hj1, hj2⟩ := first_pow hG _ hg
    obtain ⟨-, -, hw, -⟩ := local_step hp hAn ha hcent hkeyA hj1 hj2
    rcases j with _ | j
    · simpa using hw
    · exfalso
      obtain ⟨r, hr⟩ := mem_zpowers_iff.mp (hAn.conj_mem a (mem_zpowers a) (g ^ 2 ^ j))
      have h1 : g ^ 2 ^ (j + 1) * a * (g ^ 2 ^ (j + 1))⁻¹
          = g ^ 2 ^ j * (g ^ 2 ^ j * a * (g ^ 2 ^ j)⁻¹) * (g ^ 2 ^ j)⁻¹ := by
        rw [pow_succ, pow_mul]; group
      rw [← hr, ← conj_zpow, ← hr, ← zpow_mul, hw, ← zpow_neg_one,
        zpow_eq_zpow_iff_modEq, hoa] at h1
      have h4d : (4 : ℤ) ∣ 2 ^ n := by
        have := pow_dvd_pow (2 : ℤ) hn2; norm_num at this; exact this
      have h4 : r * r ≡ -1 [ZMOD 4] := Int.ModEq.of_dvd h4d h1.symm
      have h5 : r % 4 = 0 ∨ r % 4 = 1 ∨ r % 4 = 2 ∨ r % 4 = 3 := by omega
      unfold Int.ModEq at h4
      rw [Int.mul_emod] at h4
      rcases h5 with h | h | h | h <;> rw [h] at h4 <;> norm_num at h4
  have hcommk : ∀ z, z ∉ zpowers a → ∀ k : ℤ, z * a ^ k = a ^ (-k) * z := by
    intro z hz k
    have h := hinv z hz
    have : z * a ^ k * z⁻¹ = a ^ (-k) := by rw [← conj_zpow, h, inv_zpow, zpow_neg]
    rw [← this]; group
  have hcommk' : ∀ z, z ∉ zpowers a → ∀ k : ℤ, a ^ k * z = z * a ^ (-k) := by
    intro z hz k
    rw [hcommk z hz (-k), neg_neg]
  -- the explicit isomorphism
  set m := n - 1 with hm
  have hN : orderOf a = 2 * 2 ^ m := by rw [ha, hm, ← pow_succ']; congr 1; omega
  have hoa' : ((orderOf a : ℕ) : ℤ) = ((2 * 2 ^ m : ℕ) : ℤ) := by rw [hN]
  have E : ∀ (i : ZMod (2 * 2 ^ m)) (k : ℤ), (k : ZMod (2 * 2 ^ m)) = i →
      a ^ (i.val : ℤ) = a ^ k := by
    intro i k hk
    rw [zpow_eq_zpow_iff_modEq, hoa', ← ZMod.intCast_eq_intCast_iff, hk]
    simp
  have E' : ∀ (i j : ZMod (2 * 2 ^ m)), a ^ (i.val : ℤ) = a ^ (j.val : ℤ) → i = j := by
    intro i j h
    rw [zpow_eq_zpow_iff_modEq, hoa', ← ZMod.intCast_eq_intCast_iff] at h
    simpa using h
  let f : QuaternionGroup (2 ^ m) → G := fun q =>
    match q with
    | .a i => a ^ (i.val : ℤ)
    | .xa i => y * a ^ (i.val : ℤ)
  have hf : ∀ q₁ q₂, f (q₁ * q₂) = f q₁ * f q₂ := by
    intro q₁ q₂
    cases q₁ with
    | a i =>
      cases q₂ with
      | a j =>
        simp only [f, QuaternionGroup.a_mul_a]
        rw [← zpow_add]; apply E; push_cast; simp
      | xa j =>
        simp only [f, QuaternionGroup.a_mul_xa]
        rw [← mul_assoc, hcommk' y hi1, mul_assoc, ← zpow_add]
        congr 1; apply E; push_cast; simp only [ZMod.natCast_val, ZMod.cast_id', id_eq]; ring
    | xa i =>
      cases q₂ with
      | a j =>
        simp only [f, QuaternionGroup.xa_mul_a]
        rw [mul_assoc, ← zpow_add]
        congr 1; apply E; push_cast; simp
      | xa j =>
        simp only [f, QuaternionGroup.xa_mul_xa]
        rw [show y * a ^ (i.val : ℤ) * (y * a ^ (j.val : ℤ))
            = y * (a ^ (i.val : ℤ) * y) * a ^ (j.val : ℤ) by group,
          hcommk' y hi1, ← mul_assoc, ← pow_two, hy2, mul_assoc, ← zpow_add,
          ← zpow_natCast, ← zpow_add]
        apply E; push_cast; simp only [ZMod.natCast_val, ZMod.cast_id', id_eq]; ring
  let F : QuaternionGroup (2 ^ m) →* G := MonoidHom.mk' f hf
  have hinj : Function.Injective F := by
    intro q₁ q₂ h
    change f q₁ = f q₂ at h
    cases q₁ with
    | a i =>
      cases q₂ with
      | a j => simp only [f] at h; rw [E' i j h]
      | xa j =>
        exfalso; simp only [f] at h
        apply hi1
        rw [show y = a ^ (i.val : ℤ) * (a ^ (j.val : ℤ))⁻¹ by rw [h]; group]
        exact mul_mem (zpow_mem (mem_zpowers a) _) (inv_mem (zpow_mem (mem_zpowers a) _))
    | xa i =>
      cases q₂ with
      | a j =>
        exfalso; simp only [f] at h
        apply hi1
        rw [show y = a ^ (j.val : ℤ) * (a ^ (i.val : ℤ))⁻¹ by rw [← h]; group]
        exact mul_mem (zpow_mem (mem_zpowers a) _) (inv_mem (zpow_mem (mem_zpowers a) _))
      | xa j => simp only [f] at h; rw [E' i j (mul_left_cancel h)]
  have hsurj : Function.Surjective F := by
    intro g
    by_cases hg : g ∈ zpowers a
    · obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
      exact ⟨.a (k : ZMod (2 * 2 ^ m)), E _ k rfl⟩
    · have hmem : y⁻¹ * g ∈ zpowers a := by
        apply hcent
        rw [mem_centralizer_iff]
        intro h hh
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hh
        have e1 := hcommk g hg k
        have e2 := hcommk y hi1 k
        have e3 : a ^ k * y⁻¹ = y⁻¹ * a ^ (-k) := by
          rw [show a ^ (-k) = y * a ^ k * y⁻¹ by rw [e2]; group]; group
        rw [← mul_assoc, e3, mul_assoc, ← e1, mul_assoc]
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmem
      refine ⟨.xa (k : ZMod (2 * 2 ^ m)), ?_⟩
      change y * a ^ ((k : ZMod (2 * 2 ^ m)).val : ℤ) = g
      rw [E _ k rfl, hk]; group
  right
  exact ⟨m, by omega, ⟨(MulEquiv.ofBijective F ⟨hinj, hsurj⟩).symm⟩⟩
