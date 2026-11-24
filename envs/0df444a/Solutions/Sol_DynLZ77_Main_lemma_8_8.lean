-- Prove2me | solution 1 for DynLZ77.Main.lemma_8_8
-- status  : ACCEPTED   (prove)
-- author  : @matan3
-- created : 2026-11-24T13:56:25.417546+00:00
-- url     : https://prove2.me/submissions/b8a20536-2ae5-4c3d-a757-1f9b0fba07c1

import Mathlib
import Definitions.Def_DynLZ77_Main_Strings
import Definitions.Def_DynLZ77_Main_Structure

set_option autoImplicit false

namespace DynLZ77.Main.Lemma88

variable {α : Type}

/-- `q` is a period of the 0-based window `[a, b)` of `S`: `S[x] = S[x + q]` whenever
`a ≤ x` and `x + q < b`. -/
def PerOn (S : List α) (a b q : ℕ) : Prop :=
  ∀ x, a ≤ x → x + q < b → S[x]? = S[x + q]?

theorem PerOn.mono {S : List α} {a b a' b' q : ℕ} (h : PerOn S a b q) (ha : a ≤ a')
    (hb : b' ≤ b) : PerOn S a' b' q :=
  fun x hx hxq => h x (by omega) (by omega)

/-- Multiples of a period are periods. -/
theorem PerOn.mul {S : List α} {a b q : ℕ} (h : PerOn S a b q) (k : ℕ) :
    PerOn S a b (k * q) := by
  induction k with
  | zero => intro x _ _; simp
  | succ k ih =>
    intro x hx hxq
    rw [show (k + 1) * q = k * q + q by ring] at hxq ⊢
    generalize k * q = m at ih hxq ⊢
    rw [h x hx (by omega), ih (x + q) (by omega) (by omega), show x + q + m = x + (m + q) by omega]

/-- One Euclid step of the (weak) periodicity lemma. -/
theorem PerOn.sub {S : List α} {a b q q' : ℕ} (h : PerOn S a b q) (h' : PerOn S a b q')
    (hlt : q < q') (hlen : a + q + q' ≤ b) : PerOn S a b (q' - q) := by
  intro x hx hxq
  by_cases hc : x + q' < b
  · rw [h' x hx hc, h (x + (q' - q)) (by omega) (by omega), show x + (q' - q) + q = x + q' by omega]
  · have h1 := h (x - q) (by omega) (by omega)
    have h2 := h' (x - q) (by omega) (by omega)
    rw [show x - q + q = x by omega] at h1
    rw [show x - q + q' = x + (q' - q) by omega] at h2
    rw [← h1, h2]

/-- Weak periodicity lemma: if a window of length at least `q + q'` has periods `q` and `q'`,
it has period `gcd(q, q')`. -/
theorem PerOn.gcd {S : List α} {a b : ℕ} (n : ℕ) :
    ∀ q q', q + q' = n → PerOn S a b q → PerOn S a b q' → 1 ≤ q → 1 ≤ q' →
      a + q + q' ≤ b → PerOn S a b (Nat.gcd q q') := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro q q' hn h h' hq hq' hlen
    rcases lt_trichotomy q q' with hlt | heq | hgt
    · have := ih q' (by omega) q (q' - q) (by omega) h (h.sub h' hlt hlen) hq (by omega)
        (by omega)
      rwa [Nat.gcd_sub_self_right hlt.le] at this
    · subst heq
      rwa [Nat.gcd_self]
    · have := ih q (by omega) (q - q') q' (by omega) (h'.sub h hgt (by omega)) h' (by omega) hq'
        (by omega)
      rwa [Nat.gcd_sub_self_left hgt.le] at this

/-- A divisor `g` of a period `q` of `[a, b)` that is a period of `[a + 1, b)` is a period of
`[a, b)`. -/
theorem PerOn.extend_left {S : List α} {a b q g : ℕ} (hq : PerOn S a b q)
    (hg : PerOn S (a + 1) b g) (hdvd : g ∣ q) (hg1 : 1 ≤ g) (hq1 : 1 ≤ q) (hqb : a + q < b) :
    PerOn S a b g := by
  obtain ⟨m, rfl⟩ := hdvd
  have hm0 : m ≠ 0 := by rintro rfl; simp at hq1
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hmul := hg.mul m'
  rw [show g * (m' + 1) = m' * g + g by ring] at hq hqb
  generalize m' * g = t at hmul hq hqb
  intro x hx hxg
  by_cases hxa : x = a
  · rw [hxa, hq a le_rfl hqb, hmul (a + g) (by omega) (by omega),
      show a + g + t = a + (t + g) by omega]
  · exact hg x (by omega) hxg

/-- A divisor `g` of a period `q` of `[a, b)` that is a period of `[a, b - 1)` is a period of
`[a, b)`. -/
theorem PerOn.extend_right {S : List α} {a b q g : ℕ} (hq : PerOn S a b q)
    (hg : PerOn S a (b - 1) g) (hdvd : g ∣ q) (hg1 : 1 ≤ g) (hq1 : 1 ≤ q) (hqb : a + q < b) :
    PerOn S a b g := by
  obtain ⟨m, rfl⟩ := hdvd
  have hm0 : m ≠ 0 := by rintro rfl; simp at hq1
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hmul := hg.mul m'
  rw [show g * (m' + 1) = m' * g + g by ring] at hq hqb
  generalize m' * g = t at hmul hq hqb
  intro x hx hxg
  by_cases hlast : x + g < b - 1
  · exact hg x hx hlast
  · have h1 := hq (x - t) (by omega) (by omega)
    have h2 := hmul (x - t) (by omega) (by omega)
    rw [show x - t + (t + g) = x + g by omega] at h1
    rw [show x - t + t = x by omega] at h2
    rw [← h2, h1]

/-- `per S` is a period of `S`, and the smallest one. -/
theorem per_spec (S : List α) : IsPeriod S (per S) ∧ ∀ q, IsPeriod S q → per S ≤ q := by
  classical
  unfold per
  exact ⟨Nat.find_spec (exists_isPeriod S), fun q hq => Nat.find_min' (exists_isPeriod S) hq⟩

theorem isPeriod_iff (S : List α) (q : ℕ) :
    IsPeriod S q ↔ 1 ≤ q ∧ PerOn S 0 S.length q := by
  constructor
  · rintro ⟨hq, h⟩
    refine ⟨hq, fun x _ hxq => ?_⟩
    have h1 := h (x + 1) (by omega) (by omega)
    rw [show x + 1 - 1 = x by omega, show x + 1 + q - 1 = x + q by omega] at h1
    exact h1
  · rintro ⟨hq, h⟩
    refine ⟨hq, fun i hi hiq => ?_⟩
    have := h (i - 1) (by omega) (by omega)
    rw [show i - 1 + q = i + q - 1 by omega] at this
    exact this

/-- Periods of the window `S[s+1..s+w]` (1-based) are the periods of `[s, s + w)` (0-based). -/
theorem isPeriod_window_iff (S : List α) (s w q : ℕ) (hs : s + w ≤ S.length) :
    IsPeriod (sub S (s + 1) (s + w)) q ↔ 1 ≤ q ∧ PerOn S s (s + w) q := by
  have hsub : sub S (s + 1) (s + w) = (S.drop s).take w := by
    unfold sub
    rw [show s + 1 - 1 = s by omega, show s + w + 1 - (s + 1) = w by omega]
  rw [hsub]
  have hlen : ((S.drop s).take w).length = w := by simp; omega
  have hT : ∀ k, k < w → ((S.drop s).take w)[k]? = S[s + k]? := by
    intro k hk
    rw [List.getElem?_take_of_lt hk, List.getElem?_drop]
  constructor
  · rintro ⟨hq, h⟩
    refine ⟨hq, fun x hx hxq => ?_⟩
    have h1 := h (x - s + 1) (by omega) (by omega)
    rw [show x - s + 1 - 1 = x - s by omega, show x - s + 1 + q - 1 = x - s + q by omega,
      hT (x - s) (by omega), hT (x - s + q) (by omega), show s + (x - s) = x by omega,
      show s + (x - s + q) = x + q by omega] at h1
    exact h1
  · rintro ⟨hq, h⟩
    refine ⟨hq, fun i hi hiq => ?_⟩
    rw [hT (i - 1) (by omega), hT (i + q - 1) (by omega)]
    have := h (s + (i - 1)) (by omega) (by omega)
    rw [show s + (i - 1) + q = s + (i + q - 1) by omega] at this
    exact this

/-- If every length-`w` window has smallest period `< P` and `2P ≤ w`, all windows have the
same smallest period. -/
theorem windows_const (S : List α) (P w : ℕ) (hwP : 2 * P ≤ w)
    (hsmall : ∀ s, s + w ≤ S.length → per (sub S (s + 1) (s + w)) < P) :
    ∀ s, s + w ≤ S.length → per (sub S (s + 1) (s + w)) = per (sub S (0 + 1) (0 + w)) := by
  intro s
  induction s with
  | zero => intro _; rfl
  | succ s ih =>
    intro hs
    have hr := ih (by omega)
    set r := per (sub S (0 + 1) (0 + w)) with hr_def
    have hWs : PerOn S s (s + w) r := by
      have := (per_spec (sub S (s + 1) (s + w))).1
      rw [hr] at this
      exact ((isPeriod_window_iff S s w r (by omega)).1 this).2
    have hr1 : 1 ≤ r := by have := (per_spec (sub S (s + 1) (s + w))).1.1; omega
    have hrP : r < P := by have := hsmall s (by omega); omega
    set r' := per (sub S (s + 1 + 1) (s + 1 + w)) with hr'_def
    have hWs1 : PerOn S (s + 1) (s + 1 + w) r' :=
      ((isPeriod_window_iff S (s + 1) w r' hs).1 (per_spec _).1).2
    have hr'1 : 1 ≤ r' := (per_spec _).1.1
    have hr'P : r' < P := hsmall (s + 1) hs
    have hO1 : PerOn S (s + 1) (s + w) r := hWs.mono (by omega) le_rfl
    have hO2 : PerOn S (s + 1) (s + w) r' := hWs1.mono le_rfl (by omega)
    have hg := PerOn.gcd (r + r') r r' rfl hO1 hO2 hr1 hr'1 (by omega)
    have hg1 : 1 ≤ Nat.gcd r r' := Nat.gcd_pos_of_pos_left _ hr1
    have hgr : Nat.gcd r r' ≤ r := Nat.le_of_dvd hr1 (Nat.gcd_dvd_left r r')
    have hgr' : Nat.gcd r r' ≤ r' := Nat.le_of_dvd hr'1 (Nat.gcd_dvd_right r r')
    have hL : PerOn S s (s + w) (Nat.gcd r r') :=
      PerOn.extend_left hWs hg (Nat.gcd_dvd_left r r') hg1 hr1 (by omega)
    have hpL := (per_spec (sub S (s + 1) (s + w))).2 _
      ((isPeriod_window_iff S s w _ (by omega)).2 ⟨hg1, hL⟩)
    rw [hr] at hpL
    have hg' : PerOn S (s + 1) (s + 1 + w - 1) (Nat.gcd r r') := by
      rw [show s + 1 + w - 1 = s + w by omega]
      exact hg
    have hR : PerOn S (s + 1) (s + 1 + w) (Nat.gcd r r') :=
      PerOn.extend_right hWs1 hg' (Nat.gcd_dvd_right r r') hg1 hr'1 (by omega)
    have hpR := (per_spec (sub S (s + 1 + 1) (s + 1 + w))).2 _
      ((isPeriod_window_iff S (s + 1) w _ hs).2 ⟨hg1, hR⟩)
    omega

end DynLZ77.Main.Lemma88

open DynLZ77.Main DynLZ77.Main.Lemma88

theorem solution {α : Type} (S : List α) (p : ℤ) (hp : p ≤ (per S : ℤ)) (w : ℕ)
    (hw1 : 2 * p ≤ (w : ℤ)) (hw2 : w ≤ S.length) :
    ∃ i : ℕ, 1 ≤ i ∧ i + w ≤ S.length + 1 ∧ p ≤ (per (sub S i (i + w - 1)) : ℤ) := by
  by_cases hp1 : p ≤ 1
  · refine ⟨1, le_rfl, by omega, ?_⟩
    have := (per_spec (sub S 1 (1 + w - 1))).1.1
    omega
  push Not at hp1
  obtain ⟨P, rfl⟩ : ∃ P : ℕ, p = P := ⟨p.toNat, by omega⟩
  have hP : P ≤ per S := by omega
  have hwP : 2 * P ≤ w := by omega
  by_contra hcon
  push Not at hcon
  have hsmall : ∀ s, s + w ≤ S.length → per (sub S (s + 1) (s + w)) < P := by
    intro s hs
    have := hcon (s + 1) (by omega) (by omega)
    rw [show s + 1 + w - 1 = s + w by omega] at this
    omega
  have hconst := windows_const S P w hwP hsmall
  set r := per (sub S (0 + 1) (0 + w)) with hr_def
  have hr1 : 1 ≤ r := (per_spec _).1.1
  have hrP : r < P := hsmall 0 (by omega)
  have hper : IsPeriod S r := by
    refine (isPeriod_iff S r).2 ⟨hr1, fun x _ hxr => ?_⟩
    obtain ⟨s, hs, hsx, hxs⟩ : ∃ s, s + w ≤ S.length ∧ s ≤ x ∧ x + r < s + w := by
      by_cases hxw : x + w ≤ S.length
      · exact ⟨x, hxw, le_rfl, by omega⟩
      · exact ⟨S.length - w, by omega, by omega, by omega⟩
    have hW := (per_spec (sub S (s + 1) (s + w))).1
    rw [hconst s hs] at hW
    exact ((isPeriod_window_iff S s w r hs).1 hW).2 x hsx hxs
  have := (per_spec S).2 r hper
  omega
