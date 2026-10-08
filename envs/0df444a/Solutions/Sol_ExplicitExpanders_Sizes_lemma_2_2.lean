-- Prove2me | solution 1 for ExplicitExpanders.Sizes.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T17:57:55.920979+00:00
-- url     : https://prove2.me/submissions/b349f33b-1bf5-4b70-80e7-0570fcdc899a

import Mathlib
import Definitions.Def_ExplicitExpanders_Sizes_Q

set_option autoImplicit false

namespace FC35708B

open Filter

/-- Covering: if `R^j < P^i ≤ (1+μ) R^j`, then eventually every `n` has an element
`C P^a R^b` in `[n, (1+μ) n]`. -/
theorem cover (P R C : ℕ) (hR : 2 ≤ R) (hC : 0 < C) (i j : ℕ) (μ : ℝ)
    (hlt : R ^ j < P ^ i) (hle : ((P ^ i : ℕ) : ℝ) ≤ (1 + μ) * ((R ^ j : ℕ) : ℝ)) :
    ∀ᶠ n : ℕ in atTop, ∃ a b : ℕ, n ≤ C * P ^ a * R ^ b ∧
      ((C * P ^ a * R ^ b : ℕ) : ℝ) ≤ (1 + μ) * (n : ℝ) := by
  classical
  have hRj : 0 < R ^ j := pos_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
  have hRjR : (0 : ℝ) < ((R ^ j : ℕ) : ℝ) := by exact_mod_cast hRj
  have hμ : 0 < μ := by
    have h1 : ((R ^ j : ℕ) : ℝ) < ((P ^ i : ℕ) : ℝ) := by exact_mod_cast hlt
    nlinarith
  have hratio : (1 : ℝ) < ((P ^ i : ℕ) : ℝ) / ((R ^ j : ℕ) : ℝ) := by
    rw [one_lt_div hRjR]; exact_mod_cast hlt
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (R : ℝ) hratio
  have hK' : R * R ^ (j * K) < P ^ (i * K) := by
    rw [div_pow, lt_div_iff₀ (by positivity)] at hK
    rw [pow_mul, pow_mul]
    exact_mod_cast hK
  filter_upwards [eventually_ge_atTop (C * R ^ (j * K))] with n hn
  have hex : ∃ b, n < C * R ^ b := ⟨n, by
    have h1 : n < R ^ n := Nat.lt_pow_self (by omega)
    calc n < R ^ n := h1
      _ ≤ C * R ^ n := Nat.le_mul_of_pos_left _ hC⟩
  set b0 := Nat.find hex with hb0def
  have hb0 : n < C * R ^ b0 := Nat.find_spec hex
  have hjK : j * K < b0 := by
    by_contra hcon
    push Not at hcon
    have : C * R ^ b0 ≤ C * R ^ (j * K) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hcon)
    omega
  obtain ⟨b, hb⟩ : ∃ b, b0 = b + 1 := ⟨b0 - 1, by omega⟩
  have hbmin : C * R ^ b ≤ n := by
    have := Nat.find_min hex (show b < b0 by omega)
    omega
  have hjKb : j * K ≤ b := by omega
  let v : ℕ → ℕ := fun k => C * P ^ (i * k) * R ^ (b - j * k)
  have hvK : n ≤ v K := by
    have e : R ^ (b - j * K) * R ^ (j * K) = R ^ b := by
      rw [← pow_add, Nat.sub_add_cancel hjKb]
    have hpos : 0 < R ^ (j * K) := pos_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
    have hCRb : 0 < C * R ^ b := Nat.mul_pos hC (pos_iff_ne_zero.mpr (pow_ne_zero _ (by omega)))
    have h2 : n * R ^ (j * K) < v K * R ^ (j * K) := by
      have h3 : v K * R ^ (j * K) = C * R ^ b * P ^ (i * K) := by
        simp only [v]; rw [← e]; ring
      rw [h3]
      calc n * R ^ (j * K) < C * R ^ b0 * R ^ (j * K) := Nat.mul_lt_mul_of_pos_right hb0 hpos
        _ = C * R ^ b * (R * R ^ (j * K)) := by rw [hb, pow_succ]; ring
        _ < C * R ^ b * P ^ (i * K) := Nat.mul_lt_mul_of_pos_left hK' hCRb
    exact le_of_lt (lt_of_mul_lt_mul_right h2 (Nat.zero_le _))
  have hexk : ∃ k, n ≤ v k := ⟨K, hvK⟩
  set k0 := Nat.find hexk with hk0def
  have hk0 : n ≤ v k0 := Nat.find_spec hexk
  have hk0K : k0 ≤ K := Nat.find_min' hexk hvK
  refine ⟨i * k0, b - j * k0, hk0, ?_⟩
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rcases Nat.eq_zero_or_eq_succ_pred k0 with h0 | h0
  · -- k0 = 0: v 0 = C R^b ≤ n
    have hv0 : v k0 = C * R ^ b := by simp only [v]; rw [h0]; simp
    have : v k0 = n := by omega
    show ((v k0 : ℕ) : ℝ) ≤ (1 + μ) * n
    rw [this]; nlinarith
  · set k := k0.pred with hkdef
    have hk : v k < n := by
      have := Nat.find_min hexk (show k < k0 by omega)
      omega
    have hjk1 : j * (k + 1) ≤ b := le_trans (Nat.mul_le_mul_left _ (by omega)) hjKb
    have hid : v (k + 1) * R ^ j = v k * P ^ i := by
      simp only [v]
      have e1 : j * (k + 1) = j * k + j := by ring
      have e2 : b - j * k = (b - j * (k + 1)) + j := by rw [e1] at hjk1 ⊢; omega
      rw [e2, pow_add, mul_add, mul_one, pow_add]; ring
    have hidR : ((v (k + 1) : ℕ) : ℝ) * ((R ^ j : ℕ) : ℝ) = ((v k : ℕ) : ℝ) * ((P ^ i : ℕ) : ℝ) := by
      exact_mod_cast hid
    have hkR : ((v k : ℕ) : ℝ) < n := by exact_mod_cast hk
    have hvk0 : (0 : ℝ) ≤ ((v k : ℕ) : ℝ) := Nat.cast_nonneg _
    have key : ((v (k + 1) : ℕ) : ℝ) * ((R ^ j : ℕ) : ℝ) ≤ (1 + μ) * n * ((R ^ j : ℕ) : ℝ) := by
      rw [hidR]
      calc ((v k : ℕ) : ℝ) * ((P ^ i : ℕ) : ℝ) ≤ ((v k : ℕ) : ℝ) * ((1 + μ) * ((R ^ j : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left hle hvk0
        _ ≤ n * ((1 + μ) * ((R ^ j : ℕ) : ℝ)) := by
            apply mul_le_mul_of_nonneg_right hkR.le; positivity
        _ = (1 + μ) * n * ((R ^ j : ℕ) : ℝ) := by ring
    have hfin := le_of_mul_le_mul_right key hRjR
    have hk1 : k + 1 = k0 := by omega
    rw [hk1] at hfin
    exact hfin

theorem two_le_cube {q : ℕ} (hq : q.Prime) : 2 ≤ q ^ 3 :=
  le_trans hq.two_le (Nat.le_self_pow (by norm_num) q)

/-- Distinct primes: `q₁^a = q₂^b` with `a > 0` is impossible. -/
theorem pow_ne_pow_of_primes {q₁ q₂ : ℕ} (hq₁ : q₁.Prime) (hq₂ : q₂.Prime) (hne : q₁ ≠ q₂)
    (a b : ℕ) (ha : 0 < a) : q₁ ^ a ≠ q₂ ^ b := by
  intro h
  have h1 : q₁ ∣ q₂ ^ b := h ▸ dvd_pow_self q₁ (by omega)
  exact hne ((Nat.prime_dvd_prime_iff_eq hq₁ hq₂).mp (hq₁.dvd_of_dvd_pow h1))

/-- Dirichlet approximation gives a near-one ratio between powers of `q₁³` and `q₂³`. -/
theorem approx {q₁ q₂ : ℕ} (hq₁ : q₁.Prime) (hq₂ : q₂.Prime) (hne : q₁ ≠ q₂) (μ : ℝ) (hμ : 0 < μ) :
    ∃ i j : ℕ, ((q₂ ^ 3) ^ j < (q₁ ^ 3) ^ i ∧
        (((q₁ ^ 3) ^ i : ℕ) : ℝ) ≤ (1 + μ) * (((q₂ ^ 3) ^ j : ℕ) : ℝ)) ∨
      ((q₁ ^ 3) ^ j < (q₂ ^ 3) ^ i ∧
        (((q₂ ^ 3) ^ i : ℕ) : ℝ) ≤ (1 + μ) * (((q₁ ^ 3) ^ j : ℕ) : ℝ)) := by
  have h1q : (1 : ℝ) < (q₁ ^ 3 : ℕ) := by
    have := two_le_cube hq₁; exact_mod_cast (by omega : 1 < q₁ ^ 3)
  have h2q : (1 : ℝ) < (q₂ ^ 3 : ℕ) := by
    have := two_le_cube hq₂; exact_mod_cast (by omega : 1 < q₂ ^ 3)
  set α := Real.log ((q₁ ^ 3 : ℕ) : ℝ) with hα
  set β := Real.log ((q₂ ^ 3 : ℕ) : ℝ) with hβ
  have hαp : 0 < α := Real.log_pos h1q
  have hβp : 0 < β := Real.log_pos h2q
  have hlμ : 0 < Real.log (1 + μ) := Real.log_pos (by linarith)
  obtain ⟨N, hN⟩ := exists_nat_gt (β / Real.log (1 + μ))
  obtain ⟨j, k, hk, -, hjk⟩ := Real.exists_int_int_abs_mul_sub_le (α / β) (Nat.succ_pos N)
  have hNp : (0 : ℝ) < ((N.succ : ℕ) : ℝ) + 1 := by positivity
  have hsmall : β * (1 / (((N.succ : ℕ) : ℝ) + 1)) < Real.log (1 + μ) := by
    rw [mul_one_div, div_lt_iff₀ hNp]
    rw [div_lt_iff₀ hlμ] at hN
    push_cast
    nlinarith
  have hle1 : 1 / (((N.succ : ℕ) : ℝ) + 1) ≤ 1 := by
    rw [div_le_one hNp]; push_cast; linarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)]
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hj0 : 0 ≤ j := by
    have hxpos : 0 < (k : ℝ) * (α / β) := mul_pos hkpos (div_pos hαp hβp)
    have := (abs_le.mp hjk).2
    have : (-1 : ℝ) < (j : ℝ) := by linarith
    have : (-1 : ℤ) < j := by exact_mod_cast this
    omega
  obtain ⟨jn, rfl⟩ := Int.eq_ofNat_of_zero_le hj0
  obtain ⟨kn, rfl⟩ := Int.eq_ofNat_of_zero_le hk.le
  have hkn : 0 < kn := by exact_mod_cast hk
  -- (cast normalization happens below)
  -- L = kn α - jn β
  have hL : |(kn : ℝ) * α - (jn : ℝ) * β| < Real.log (1 + μ) := by
    have e : (kn : ℝ) * α - (jn : ℝ) * β = β * ((kn : ℝ) * (α / β) - jn) := by
      field_simp
    rw [e, abs_mul, abs_of_pos hβp]
    calc β * |(kn : ℝ) * (α / β) - jn| ≤ β * (1 / (((N.succ : ℕ) : ℝ) + 1)) := by
          apply mul_le_mul_of_nonneg_left _ hβp.le
          push_cast; push_cast at hjk; exact hjk
      _ < Real.log (1 + μ) := hsmall
  set X : ℝ := (((q₁ ^ 3) ^ kn : ℕ) : ℝ) with hX
  set Y : ℝ := (((q₂ ^ 3) ^ jn : ℕ) : ℝ) with hY
  have hXp : 0 < X := by rw [hX]; exact Nat.cast_pos.mpr (pow_pos (pow_pos hq₁.pos 3) kn)
  have hYp : 0 < Y := by rw [hY]; exact Nat.cast_pos.mpr (pow_pos (pow_pos hq₂.pos 3) jn)
  have hlX : Real.log X = (kn : ℝ) * α := by rw [hX, hα]; push_cast; rw [Real.log_pow]
  have hlY : Real.log Y = (jn : ℝ) * β := by rw [hY, hβ]; push_cast; rw [Real.log_pow]
  have hXY : X ≠ Y := by
    rw [hX, hY]
    intro h
    have h' : (q₁ ^ 3) ^ kn = (q₂ ^ 3) ^ jn := by exact_mod_cast h
    rw [← pow_mul, ← pow_mul] at h'
    exact pow_ne_pow_of_primes hq₁ hq₂ hne _ _ (by omega) h'
  have h1μ : (0 : ℝ) < 1 + μ := by linarith
  rcases lt_or_gt_of_ne hXY with hlt | hgt
  · -- X < Y : second orientation, i = jn, j = kn
    refine ⟨jn, kn, Or.inr ⟨?_, ?_⟩⟩
    · have : X < Y := hlt
      rw [hX, hY] at this; exact_mod_cast this
    · show Y ≤ (1 + μ) * X
      have hlog : Real.log Y < Real.log ((1 + μ) * X) := by
        rw [Real.log_mul h1μ.ne' hXp.ne', hlX, hlY]
        have := (abs_lt.mp hL).1
        linarith
      exact ((Real.log_lt_log_iff hYp (by positivity)).mp hlog).le
  · refine ⟨kn, jn, Or.inl ⟨?_, ?_⟩⟩
    · have : Y < X := hgt
      rw [hX, hY] at this; exact_mod_cast this
    · show X ≤ (1 + μ) * Y
      have hlog : Real.log X < Real.log ((1 + μ) * Y) := by
        rw [Real.log_mul h1μ.ne' hYp.ne', hlX, hlY]
        have := (abs_lt.mp hL).2
        linarith
      exact ((Real.log_lt_log_iff hXp (by positivity)).mp hlog).le

open ExplicitExpanders.Sizes in
theorem Q_eq (q₁ q₂ a b : ℕ) :
    Q q₁ q₂ (a + 1) (b + 1) =
      ((q₁ * (q₁ - 1) * (q₁ + 1) / 2) * (q₂ * (q₂ - 1) * (q₂ + 1) / 2)) * (q₁ ^ 3) ^ a * (q₂ ^ 3) ^ b := by
  simp only [Q, Nat.add_sub_cancel, ← pow_mul]; ring

open ExplicitExpanders.Sizes in
theorem key {q₁ q₂ : ℕ} (hq₁ : q₁.Prime) (hq₂ : q₂.Prime) (hne : q₁ ≠ q₂) (μ : ℝ) (hμ : 0 < μ) :
    ∀ᶠ n : ℕ in atTop, ∃ s t : ℕ, 1 ≤ s ∧ 1 ≤ t ∧ n ≤ Q q₁ q₂ s t ∧
      (Q q₁ q₂ s t : ℝ) ≤ (1 + μ) * (n : ℝ) := by
  set C := (q₁ * (q₁ - 1) * (q₁ + 1) / 2) * (q₂ * (q₂ - 1) * (q₂ + 1) / 2) with hCdef
  have hc : ∀ q : ℕ, q.Prime → 0 < q * (q - 1) * (q + 1) / 2 := by
    intro q hq
    have h2 := hq.two_le
    apply Nat.div_pos _ (by norm_num)
    have : 2 ≤ q * (q - 1) := by
      have : 1 ≤ q - 1 := by omega
      nlinarith
    nlinarith
  have hC : 0 < C := Nat.mul_pos (hc q₁ hq₁) (hc q₂ hq₂)
  have h1 : 2 ≤ q₁ ^ 3 := FC35708B.two_le_cube hq₁
  have h2 : 2 ≤ q₂ ^ 3 := two_le_cube hq₂
  obtain ⟨i, j, h | h⟩ := approx hq₁ hq₂ hne μ hμ
  · filter_upwards [cover (q₁ ^ 3) (q₂ ^ 3) C h2 hC i j μ h.1 h.2] with n ⟨a, b, ha, hb⟩
    refine ⟨a + 1, b + 1, by omega, by omega, ?_, ?_⟩
    · rw [Q_eq]; exact ha
    · rw [Q_eq]; exact hb
  · filter_upwards [cover (q₂ ^ 3) (q₁ ^ 3) C h1 hC i j μ h.1 h.2] with n ⟨a, b, ha, hb⟩
    have e : Q q₁ q₂ (b + 1) (a + 1) = C * (q₂ ^ 3) ^ a * (q₁ ^ 3) ^ b := by
      rw [Q_eq]; ring
    refine ⟨b + 1, a + 1, by omega, by omega, ?_, ?_⟩
    · rw [e]; exact ha
    · rw [e]; exact hb

end FC35708B

open Filter Asymptotics ExplicitExpanders.Sizes in
theorem solution {q₁ q₂ : ℕ} (hq₁ : q₁.Prime) (hq₂ : q₂.Prime) (hne : q₁ ≠ q₂) :
    ∃ g : ℕ → ℝ, g =o[atTop] (fun n : ℕ => (n : ℝ)) ∧
      ∀ᶠ n : ℕ in atTop, ∃ s t : ℕ, 1 ≤ s ∧ 1 ≤ t ∧
        n ≤ Q q₁ q₂ s t ∧ (Q q₁ q₂ s t : ℝ) ≤ (n : ℝ) + g n := by
  classical
  have hex : ∀ n : ℕ, ∃ m, n ≤ m ∧ ∃ s t : ℕ, 1 ≤ s ∧ 1 ≤ t ∧ Q q₁ q₂ s t = m := by
    intro n
    refine ⟨Q q₁ q₂ (n + 1) 1, ?_, n + 1, 1, by omega, le_refl _, rfl⟩
    rw [FC35708B.Q_eq]
    have hc : ∀ q : ℕ, q.Prime → 0 < q * (q - 1) * (q + 1) / 2 := by
      intro q hq
      have h2 := hq.two_le
      apply Nat.div_pos _ (by norm_num)
      have : 2 ≤ q * (q - 1) := by
        have : 1 ≤ q - 1 := by omega
        nlinarith
      nlinarith
    have h1 : 2 ≤ q₁ ^ 3 := FC35708B.two_le_cube hq₁
    have hlt : n < (q₁ ^ 3) ^ n := Nat.lt_pow_self (by omega)
    have hC : 1 ≤ (q₁ * (q₁ - 1) * (q₁ + 1) / 2) * (q₂ * (q₂ - 1) * (q₂ + 1) / 2) :=
      Nat.mul_pos (hc q₁ hq₁) (hc q₂ hq₂)
    simp only [pow_zero, mul_one]
    nlinarith
  refine ⟨fun n => ((Nat.find (hex n) : ℕ) : ℝ) - n, ?_, ?_⟩
  · rw [isLittleO_iff]
    intro c hc
    filter_upwards [FC35708B.key hq₁ hq₂ hne c hc] with n ⟨s, t, hs, ht, hn, hQ⟩
    have hspec := (Nat.find_spec (hex n)).1
    have hmin : Nat.find (hex n) ≤ Q q₁ q₂ s t := Nat.find_min' (hex n) ⟨hn, s, t, hs, ht, rfl⟩
    have hspecR : (n : ℝ) ≤ (Nat.find (hex n) : ℝ) := by exact_mod_cast hspec
    have hminR : (Nat.find (hex n) : ℝ) ≤ (Q q₁ q₂ s t : ℝ) := by exact_mod_cast hmin
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith),
      abs_of_nonneg (Nat.cast_nonneg n)]
    nlinarith
  · filter_upwards with n
    obtain ⟨hle, s, t, hs, ht, hQ⟩ := Nat.find_spec (hex n)
    refine ⟨s, t, hs, ht, hQ ▸ hle, ?_⟩
    rw [hQ]; linarith
