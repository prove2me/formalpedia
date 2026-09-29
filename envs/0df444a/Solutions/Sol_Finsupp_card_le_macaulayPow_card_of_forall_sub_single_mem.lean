-- Prove2me | solution 1 for Finsupp.card_le_macaulayPow_card_of_forall_sub_single_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/fc1f53e1-19ed-5c67-9d5e-d9e6dac57f14

import Mathlib
import Definitions.Def_Nat_MacaulayPow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem

set_option autoImplicit false

namespace MacaulayCL

def top (d a : ℕ) : ℕ := Nat.findGreatest (fun k => k.choose (d + 1) ≤ a) (a + d + 1)

def rem (d a : ℕ) : ℕ := a - (top d a).choose (d + 1)

theorem macaulayPow_zero (a : ℕ) : Nat.macaulayPow 0 a = 0 := by simp [Nat.macaulayPow]

theorem macaulayPow_succ (d a : ℕ) :
    Nat.macaulayPow (d + 1) a = (top d a + 1).choose (d + 2) + Nat.macaulayPow d (rem d a) := by
  rw [Nat.macaulayPow]; rfl

theorem sub_le_choose (d : ℕ) : ∀ k : ℕ, k - d ≤ k.choose (d + 1)
  | 0 => by simp
  | k + 1 => by
      rw [Nat.choose_succ_succ']
      have ih := sub_le_choose d k
      rcases lt_or_ge k d with h | h
      · have : k + 1 - d = 0 := by omega
        omega
      · have hpos : 1 ≤ k.choose d := Nat.choose_pos h
        omega

theorem choose_top_le (d a : ℕ) : (top d a).choose (d + 1) ≤ a :=
  Nat.findGreatest_spec (P := fun k => k.choose (d + 1) ≤ a) (Nat.zero_le _) (by simp)

theorem lt_choose_of_top_lt (d a : ℕ) {k : ℕ} (hk : top d a < k) : a < k.choose (d + 1) := by
  rcases le_or_gt k (a + d + 1) with h | h
  · have := Nat.findGreatest_is_greatest (P := fun k => k.choose (d + 1) ≤ a) hk h
    simpa using this
  · have := sub_le_choose d k
    omega

theorem lt_choose_top_succ (d a : ℕ) : a < (top d a + 1).choose (d + 1) :=
  lt_choose_of_top_lt d a (Nat.lt_succ_self _)

theorem top_eq_of (d a k : ℕ) (h₁ : k.choose (d + 1) ≤ a) (h₂ : a < (k + 1).choose (d + 1)) :
    top d a = k := by
  apply le_antisymm
  · by_contra h
    push Not at h
    have : (k + 1).choose (d + 1) ≤ (top d a).choose (d + 1) := Nat.choose_le_choose _ h
    have := choose_top_le d a
    omega
  · by_contra h
    push Not at h
    have := lt_choose_of_top_lt d a h
    omega

theorem le_top_of_choose_le (d a k : ℕ) (h : k.choose (d + 1) ≤ a) : k ≤ top d a := by
  by_contra h'
  push Not at h'
  have := lt_choose_of_top_lt d a h'
  omega

theorem top_lt_of_lt_choose (d a k : ℕ) (h : a < k.choose (d + 1)) : top d a < k := by
  by_contra h'
  push Not at h'
  have : k.choose (d + 1) ≤ (top d a).choose (d + 1) := Nat.choose_le_choose _ h'
  have := choose_top_le d a
  omega

theorem d_le_top (d a : ℕ) : d ≤ top d a := le_top_of_choose_le d a d (by simp)

theorem top_zero_right (d : ℕ) : top d 0 = d := top_eq_of d 0 d (by simp) (by simp)

theorem d_lt_top_of_pos (d a : ℕ) (ha : 0 < a) : d < top d a := by
  have := le_top_of_choose_le d a (d + 1) (by simp; omega)
  omega

theorem top_zero_left (a : ℕ) : top 0 a = a := top_eq_of 0 a a (by simp) (by simp)

theorem rem_zero_left (a : ℕ) : rem 0 a = 0 := by simp [rem, top_zero_left]

theorem rem_zero_right (d : ℕ) : rem d 0 = 0 := by simp [rem]

theorem rem_add_choose (d a : ℕ) : rem d a + (top d a).choose (d + 1) = a := by
  unfold rem; have := choose_top_le d a; omega

theorem rem_lt (d a : ℕ) : rem d a < (top d a).choose d := by
  have h := lt_choose_top_succ d a
  rw [Nat.choose_succ_succ'] at h
  unfold rem; have := choose_top_le d a; omega

theorem macaulayPow_lt_choose : ∀ (d m r : ℕ), r < m.choose d →
    Nat.macaulayPow d r < (m + 1).choose (d + 1)
  | 0, m, r, _ => by simp [macaulayPow_zero]
  | d + 1, m, r, h => by
      rw [macaulayPow_succ]
      show _ < (m + 1).choose (d + 2)
      have hK : top d r < m := top_lt_of_lt_choose d r m h
      have hrem : Nat.macaulayPow d (rem d r) < (top d r + 1).choose (d + 1) :=
        macaulayPow_lt_choose d (top d r) (rem d r) (rem_lt d r)
      have h1 : (top d r + 1).choose (d + 2) + (top d r + 1).choose (d + 1) =
          (top d r + 2).choose (d + 2) := by
        rw [Nat.choose_succ_succ' (top d r + 1) (d + 1), add_comm]
      have h2 : (top d r + 2).choose (d + 2) ≤ (m + 1).choose (d + 2) :=
        Nat.choose_le_choose _ (by omega)
      omega

theorem macaulayPow_mono : ∀ (d : ℕ) {a b : ℕ}, a ≤ b → Nat.macaulayPow d a ≤ Nat.macaulayPow d b
  | 0, a, b, _ => by simp [macaulayPow_zero]
  | d + 1, a, b, h => by
      have ht : top d a ≤ top d b := le_top_of_choose_le d b _ ((choose_top_le d a).trans h)
      rcases ht.eq_or_lt with ht | ht
      · rw [macaulayPow_succ, macaulayPow_succ, ht]
        have hr : rem d a ≤ rem d b := by
          have ha := rem_add_choose d a; have hb := rem_add_choose d b; rw [ht] at ha; omega
        have := macaulayPow_mono d hr
        omega
      · have h1 : Nat.macaulayPow (d + 1) a < (top d a + 1 + 1).choose (d + 1 + 1) :=
          macaulayPow_lt_choose (d + 1) (top d a + 1) a (lt_choose_top_succ d a)
        have h2 : (top d a + 1 + 1).choose (d + 1 + 1) ≤ (top d b + 1).choose (d + 1 + 1) :=
          Nat.choose_le_choose _ (by omega)
        have h3 : (top d b + 1).choose (d + 1 + 1) ≤ Nat.macaulayPow (d + 1) b := by
          rw [macaulayPow_succ]; exact Nat.le_add_right _ _
        omega

theorem macaulayPow_one (a : ℕ) : Nat.macaulayPow 1 a = (a + 1).choose 2 := by
  rw [macaulayPow_succ, top_zero_left, rem_zero_left, macaulayPow_zero]; rfl

theorem macaulayPow_zero_right : ∀ d : ℕ, Nat.macaulayPow d 0 = 0
  | 0 => macaulayPow_zero 0
  | d + 1 => by
      rw [macaulayPow_succ, top_zero_right, rem_zero_right, macaulayPow_zero_right d,
        Nat.choose_eq_zero_of_lt (by omega)]

theorem top_succ_of_le (d a : ℕ) (ha : 1 ≤ a) (h : a ≤ d + 2) : top (d + 1) a = d + 2 :=
  top_eq_of (d + 1) a (d + 2) (by rw [Nat.choose_self]; exact ha)
    (by have : (d + 2 + 1).choose (d + 1 + 1) = d + 2 + 1 := Nat.choose_succ_self_right (d + 2); omega)

theorem macaulayPow_eq_self : ∀ (d a : ℕ), a ≤ d + 1 → Nat.macaulayPow (d + 1) a = a
  | d, 0, _ => macaulayPow_zero_right (d + 1)
  | 0, a + 1, h => by
      obtain rfl : a = 0 := by omega
      rw [macaulayPow_one]; rfl
  | d + 1, a + 1, h => by
      have ht : top (d + 1) (a + 1) = d + 2 := top_succ_of_le d (a + 1) (by omega) (by omega)
      have hr : rem (d + 1) (a + 1) = a := by simp [rem, ht]
      rw [macaulayPow_succ, ht, hr, macaulayPow_eq_self d a (by omega)]
      have : (d + 2 + 1).choose (d + 1 + 2) = 1 := by
        rw [show d + 1 + 2 = d + 2 + 1 by omega, Nat.choose_self]
      omega

def low : ℕ → ℕ → ℕ
  | 0, _ => 0
  | d + 1, a => (top d a - 1).choose (d + 1) + low d (rem d a)

theorem low_zero (a : ℕ) : low 0 a = 0 := rfl

theorem low_succ (d a : ℕ) : low (d + 1) a = (top d a - 1).choose (d + 1) + low d (rem d a) := rfl

theorem low_zero_right : ∀ d : ℕ, low d 0 = 0
  | 0 => rfl
  | d + 1 => by
      rw [low_succ, top_zero_right, rem_zero_right, low_zero_right d, Nat.choose_eq_zero_of_lt (by omega)]

theorem low_eq_zero : ∀ (d a : ℕ), a ≤ d + 1 → low (d + 1) a = 0
  | d, 0, _ => low_zero_right _
  | 0, a + 1, h => by
      obtain rfl : a = 0 := by omega
      rw [low_succ, top_zero_left, low_zero]; rfl
  | d + 1, a + 1, h => by
      have ht : top (d + 1) (a + 1) = d + 2 := top_succ_of_le d (a + 1) (by omega) (by omega)
      have hr : rem (d + 1) (a + 1) = a := by simp [rem, ht]
      rw [low_succ, ht, hr, low_eq_zero d a (by omega), Nat.choose_eq_zero_of_lt (by omega)]

theorem low_lt_choose : ∀ (d m r : ℕ), r < (m + 1).choose (d + 1) → d + 1 ≤ m →
    low (d + 1) r < m.choose (d + 1)
  | 0, m, r, h, hm => by
      rw [low_succ, top_zero_left, low_zero]
      simp only [zero_add, Nat.choose_one_right, add_zero] at h ⊢
      omega
  | d + 1, m, r, h, hm => by
      rw [low_succ]
      show (top (d + 1) r - 1).choose (d + 2) + low (d + 1) (rem (d + 1) r) < m.choose (d + 2)
      have hT : top (d + 1) r ≤ m := Nat.lt_succ_iff.1 (top_lt_of_lt_choose (d + 1) r (m + 1) h)
      rcases Nat.eq_zero_or_pos r with hr | hr
      · subst hr
        rw [top_zero_right, rem_zero_right, low_zero_right, Nat.choose_eq_zero_of_lt (by omega),
          zero_add]
        exact Nat.choose_pos (by omega)
      · have hT' : d + 1 < top (d + 1) r := d_lt_top_of_pos _ _ hr
        have hRlt : rem (d + 1) r < (top (d + 1) r - 1 + 1).choose (d + 1) := by
          rw [Nat.sub_add_cancel (by omega)]; exact rem_lt (d + 1) r
        have ih := low_lt_choose d (top (d + 1) r - 1) (rem (d + 1) r) hRlt (by omega)
        have h1 : (top (d + 1) r - 1).choose (d + 2) + (top (d + 1) r - 1).choose (d + 1) =
            (top (d + 1) r).choose (d + 2) := by
          have := Nat.choose_succ_succ' (top (d + 1) r - 1) (d + 1)
          rw [Nat.sub_add_cancel (show 1 ≤ top (d + 1) r by omega)] at this
          rw [add_comm]; exact this.symm
        have h2 : (top (d + 1) r).choose (d + 2) ≤ m.choose (d + 2) := Nat.choose_le_choose _ hT
        omega

theorem macaulayPow_low_add : ∀ (d a : ℕ),
    Nat.macaulayPow (d + 1) (low (d + 1) a) + a = Nat.macaulayPow (d + 1) a
  | 0, a => by
      rw [low_succ, top_zero_left, low_zero, add_zero, macaulayPow_one, macaulayPow_one,
        Nat.choose_one_right]
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · rfl
      · have h2 : (a + 1).choose 2 = a + a.choose 2 := by
          have := Nat.choose_succ_succ' a 1; rw [Nat.choose_one_right] at this; exact this
        rw [Nat.sub_add_cancel ha]; omega
  | d + 1, a => by
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · rw [low_zero_right, add_zero]
      · set T := top (d + 1) a with hT
        set R := rem (d + 1) a with hR
        have hTd : d + 1 < T := d_lt_top_of_pos _ _ ha
        have hRa : R + T.choose (d + 2) = a := rem_add_choose (d + 1) a
        have hRlt : R < T.choose (d + 1) := rem_lt (d + 1) a
        have ih := macaulayPow_low_add d R
        rw [low_succ, macaulayPow_succ (d + 1) a]
        show Nat.macaulayPow (d + 2) ((T - 1).choose (d + 2) + low (d + 1) R) + a =
          (T + 1).choose (d + 3) + Nat.macaulayPow (d + 1) R
        rcases (show T = d + 2 ∨ d + 3 ≤ T by omega) with hT2 | hT3
        ·
          have hC : (d + 2).choose (d + 1) = d + 2 := Nat.choose_succ_self_right (d + 1)
          have hR1 : R ≤ d + 1 := by rw [hT2] at hRlt; omega
          rw [hT2, show d + 2 - 1 = d + 1 from rfl, Nat.choose_succ_self, zero_add, low_eq_zero d R hR1,
            macaulayPow_zero_right, macaulayPow_eq_self d R hR1, Nat.choose_self]
          rw [hT2, Nat.choose_self] at hRa
          omega
        ·
          have hlow : low (d + 1) R < (T - 1).choose (d + 1) :=
            low_lt_choose d (T - 1) R (by rw [Nat.sub_add_cancel (by omega)]; exact hRlt) (by omega)
          have hpasc : (T - 1).choose (d + 2) + (T - 1).choose (d + 1) = T.choose (d + 2) := by
            have := Nat.choose_succ_succ' (T - 1) (d + 1)
            rw [Nat.sub_add_cancel (show 1 ≤ T by omega)] at this
            rw [add_comm]; exact this.symm
          have hpasc' : T.choose (d + 3) + T.choose (d + 2) = (T + 1).choose (d + 3) := by
            rw [Nat.choose_succ_succ' T (d + 2), add_comm]
          have htop : top (d + 1) ((T - 1).choose (d + 2) + low (d + 1) R) = T - 1 :=
            top_eq_of (d + 1) _ (T - 1) (Nat.le_add_right _ _)
              (by rw [Nat.sub_add_cancel (show 1 ≤ T by omega)]; show _ < T.choose (d + 2); omega)
          have hrem : rem (d + 1) ((T - 1).choose (d + 2) + low (d + 1) R) = low (d + 1) R := by
            simp [rem, htop]
          rw [macaulayPow_succ, htop, hrem, Nat.sub_add_cancel (show 1 ≤ T by omega)]
          show T.choose (d + 3) + Nat.macaulayPow (d + 1) (low (d + 1) R) + a = _
          omega

theorem le_choose_add_low : ∀ (d m r : ℕ), r < (m + 1).choose (d + 1) → r ≤ m.choose d + low (d + 1) r
  | 0, m, r, _ => by
      rw [low_succ, top_zero_left, low_zero, Nat.choose_zero_right, Nat.choose_one_right]; omega
  | d + 1, m, r, h => by
      rw [low_succ]
      show r ≤ m.choose (d + 1) + ((top (d + 1) r - 1).choose (d + 2) + low (d + 1) (rem (d + 1) r))
      have hT : top (d + 1) r ≤ m := Nat.lt_succ_iff.1 (top_lt_of_lt_choose (d + 1) r (m + 1) h)
      have hT1 : 1 ≤ top (d + 1) r := by have := d_le_top (d + 1) r; omega
      have hRa : rem (d + 1) r + (top (d + 1) r).choose (d + 2) = r := rem_add_choose (d + 1) r
      have hRlt : rem (d + 1) r < (top (d + 1) r - 1 + 1).choose (d + 1) := by
        rw [Nat.sub_add_cancel hT1]; exact rem_lt (d + 1) r
      have ih := le_choose_add_low d (top (d + 1) r - 1) (rem (d + 1) r) hRlt
      have h1 : (top (d + 1) r - 1).choose (d + 2) + (top (d + 1) r - 1).choose (d + 1) =
          (top (d + 1) r).choose (d + 2) := by
        have := Nat.choose_succ_succ' (top (d + 1) r - 1) (d + 1)
        rw [Nat.sub_add_cancel hT1] at this
        rw [add_comm]; exact this.symm
      have h2 : (top (d + 1) r - 1).choose (d + 1) + (top (d + 1) r - 1).choose d =
          (top (d + 1) r).choose (d + 1) := by
        have := Nat.choose_succ_succ' (top (d + 1) r - 1) d
        rw [Nat.sub_add_cancel hT1] at this
        rw [add_comm]; exact this.symm
      have h3 : (top (d + 1) r).choose (d + 1) ≤ m.choose (d + 1) := Nat.choose_le_choose _ hT
      omega

theorem le_add_low : ∀ (d a s : ℕ), a ≤ Nat.macaulayPow d s → a ≤ s + low (d + 1) a
  | 0, a, s, h => by rw [macaulayPow_zero] at h; omega
  | d + 1, a, s, h => by
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · exact Nat.zero_le _
      set T := top (d + 1) a with hT
      set R := rem (d + 1) a with hR
      have hTd : d + 1 < T := d_lt_top_of_pos _ _ ha
      have hRa : R + T.choose (d + 2) = a := rem_add_choose (d + 1) a
      have hRlt : R < T.choose (d + 1) := rem_lt (d + 1) a
      set T' := top d s with hT'
      have hs : rem d s + T'.choose (d + 1) = s := rem_add_choose d s

      have hlt : Nat.macaulayPow (d + 1) s < (T' + 1 + 1).choose (d + 1 + 1) :=
        macaulayPow_lt_choose (d + 1) (T' + 1) s (lt_choose_top_succ d s)
      have hTT' : T ≤ T' + 1 := by
        have := top_lt_of_lt_choose (d + 1) a (T' + 1 + 1) (h.trans_lt hlt); omega
      rw [low_succ]
      show a ≤ s + ((T - 1).choose (d + 2) + low (d + 1) R)
      have hpasc : (T - 1).choose (d + 2) + (T - 1).choose (d + 1) = T.choose (d + 2) := by
        have := Nat.choose_succ_succ' (T - 1) (d + 1)
        rw [Nat.sub_add_cancel (show 1 ≤ T by omega)] at this
        rw [add_comm]; exact this.symm
      rcases (show T ≤ T' ∨ T = T' + 1 by omega) with hle | heq
      ·
        have h1 : T.choose (d + 1) ≤ T'.choose (d + 1) := Nat.choose_le_choose _ hle
        have h2 : R ≤ (T - 1).choose d + low (d + 1) R :=
          le_choose_add_low d (T - 1) R (by rw [Nat.sub_add_cancel (by omega)]; exact hRlt)
        have h3 : (T - 1).choose (d + 1) + (T - 1).choose d = T.choose (d + 1) := by
          have := Nat.choose_succ_succ' (T - 1) d
          rw [Nat.sub_add_cancel (show 1 ≤ T by omega)] at this
          rw [add_comm]; exact this.symm
        omega
      ·
        have hμ : Nat.macaulayPow (d + 1) s = (T' + 1).choose (d + 2) + Nat.macaulayPow d (rem d s) :=
          macaulayPow_succ d s
        rw [← heq] at hμ
        rw [show T' = T - 1 by omega] at hs
        have hR' : R ≤ Nat.macaulayPow d (rem d s) := by omega
        have ih := le_add_low d R (rem d s) hR'
        omega

theorem macaulayPow_add_le (d b s : ℕ) (h : b + s ≤ Nat.macaulayPow d s) :
    Nat.macaulayPow (d + 1) b + (b + s) ≤ Nat.macaulayPow (d + 1) (b + s) := by
  have h1 : b ≤ low (d + 1) (b + s) := by have := le_add_low d (b + s) s h; omega
  have h2 := macaulayPow_mono (d + 1) h1
  have h3 := macaulayPow_low_add d (b + s)
  omega

theorem tower_bound : ∀ (e : ℕ) (b : ℕ → ℕ) (c : ℕ), b (e + 1) ≤ 1 → (1 ≤ b e → b (e + 1) = 1) →
    (∀ k, k + 2 ≤ e + 1 → b k ≤ Nat.macaulayPow (e - k) (b (k + 1))) →
    c ≤ Nat.macaulayPow (e + 1) (b 0) →
    c + ∑ k ∈ Finset.range (e + 2), b k ≤ Nat.macaulayPow (e + 1) (∑ k ∈ Finset.range (e + 2), b k)
  | 0, b, c, h1, h2, _, h4 => by
      have h1' : b 1 ≤ 1 := h1
      have h2' : 1 ≤ b 0 → b 1 = 1 := h2
      have h4' : c ≤ (b 0 + 1).choose 2 := by rw [macaulayPow_one] at h4; exact h4
      show c + ∑ k ∈ Finset.range 2, b k ≤ Nat.macaulayPow 1 (∑ k ∈ Finset.range 2, b k)
      rw [Finset.sum_range_succ, Finset.sum_range_one, macaulayPow_one]
      rcases Nat.eq_zero_or_pos (b 0) with h0 | h0
      · have hc : c = 0 := by rw [h0] at h4'; simpa using h4'
        rw [hc, h0, zero_add, zero_add]
        rcases (show b 1 = 0 ∨ b 1 = 1 by omega) with h | h <;> rw [h] <;> simp
      · have hb1 := h2' h0
        have hp : (b 0 + 1 + 1).choose 2 = (b 0 + 1) + (b 0 + 1).choose 2 := by
          have := Nat.choose_succ_succ' (b 0 + 1) 1; rw [Nat.choose_one_right] at this; exact this
        rw [hb1]; omega
  | e + 1, b, c, h1, h2, h3, h4 => by
      have ih := tower_bound e (fun k => b (k + 1)) (b 0) h1 h2
        (fun k hk => by have := h3 (k + 1) (by omega); rwa [show e + 1 - (k + 1) = e - k by omega] at this)
        (by have := h3 0 (by omega); rwa [Nat.sub_zero] at this)
      rw [Finset.sum_range_succ' b (e + 2)]
      have key := macaulayPow_add_le (e + 1) (b 0) (∑ k ∈ Finset.range (e + 2), b (k + 1)) ih
      rw [add_comm (b 0)] at key
      omega

variable (n : ℕ)

noncomputable def Mon (e : ℕ) : Finset (Fin (n + 1) →₀ ℕ) :=
  ((Finsupp.finite_of_degree_le (σ := Fin (n + 1)) e).subset
    (fun m (hm : m ∈ {m : Fin (n + 1) →₀ ℕ | m.degree = e}) => le_of_eq hm)).toFinset

@[scoped simp] theorem mem_Mon (e : ℕ) (m : Fin (n + 1) →₀ ℕ) : m ∈ Mon n e ↔ m.degree = e := by
  simp [Mon]

noncomputable def MonW (w e : ℕ) : Finset (Fin (n + 1) →₀ ℕ) :=
  (Mon n e).filter (fun m => ∀ i : Fin (n + 1), w ≤ (i : ℕ) → m i = 0)

theorem mem_MonW (w e : ℕ) (m : Fin (n + 1) →₀ ℕ) :
    m ∈ MonW n w e ↔ m.degree = e ∧ ∀ i : Fin (n + 1), w ≤ (i : ℕ) → m i = 0 := by
  simp [MonW]

theorem MonW_zero_succ (e : ℕ) : MonW n 0 (e + 1) = ∅ := by
  ext u
  simp only [mem_MonW, Finset.notMem_empty, iff_false, not_and]
  intro hdeg hsupp
  have : u = 0 := by
    ext i; exact hsupp i (Nat.zero_le _)
  rw [this, map_zero] at hdeg
  omega

theorem MonW_zero_right (w : ℕ) : MonW n w 0 = {0} := by
  ext u
  simp only [mem_MonW, Finset.mem_singleton, Finsupp.degree_eq_zero_iff]
  constructor
  · exact fun h => h.1
  · rintro rfl; simp

noncomputable def Bplus (w e : ℕ) (B : Finset (Fin (n + 1) →₀ ℕ)) : Finset (Fin (n + 1) →₀ ℕ) :=
  (MonW n w (e + 1)).filter (fun u => ∀ i : Fin (n + 1), 1 ≤ u i → u - Finsupp.single i 1 ∈ B)

theorem mem_Bplus (w e : ℕ) (B : Finset (Fin (n + 1) →₀ ℕ)) (u : Fin (n + 1) →₀ ℕ) :
    u ∈ Bplus n w e B ↔
      u ∈ MonW n w (e + 1) ∧ ∀ i : Fin (n + 1), 1 ≤ u i → u - Finsupp.single i 1 ∈ B := by
  simp [Bplus]

theorem Bplus_subset_MonW (w e : ℕ) (B : Finset (Fin (n + 1) →₀ ℕ)) : Bplus n w e B ⊆ MonW n w (e + 1) :=
  Finset.filter_subset _ _

variable {n}

theorem degree_sub_single (u : Fin (n + 1) →₀ ℕ) (i : Fin (n + 1)) (hu : 1 ≤ u i) :
    (u - Finsupp.single i 1).degree + 1 = u.degree := by
  conv_rhs => rw [← Finsupp.sub_add_single_one_cancel (u := u) (i := i) (by omega)]
  rw [map_add, Finsupp.degree_single]

theorem exists_one_le_of_degree_ne_zero (u : Fin (n + 1) →₀ ℕ) (hu : u.degree ≠ 0) :
    ∃ i, 1 ≤ u i := by
  rw [Finsupp.degree_eq_sum] at hu
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hu
  exact ⟨i, by omega⟩

section Compression

variable (i c : Fin (n + 1))

noncomputable def mv (u : Fin (n + 1) →₀ ℕ) (j : ℕ) : Fin (n + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun l => if l = i then j else if l = c then u i + u c - j else u l

noncomputable def key (u : Fin (n + 1) →₀ ℕ) : Fin (n + 1) →₀ ℕ := mv i c u 0

noncomputable def J (A : Finset (Fin (n + 1) →₀ ℕ)) (m : Fin (n + 1) →₀ ℕ) : Finset ℕ :=
  (Finset.range (m c + 1)).filter fun j => mv i c m j ∈ A

noncomputable def comp (A : Finset (Fin (n + 1) →₀ ℕ)) : Finset (Fin (n + 1) →₀ ℕ) :=
  (A.image (key i c)).biUnion fun m => (Finset.range (J i c A m).card).image (mv i c m)

def wt (u : Fin (n + 1) →₀ ℕ) : ℕ := ∑ l ∈ Finset.univ.erase c, u l

def pot (A : Finset (Fin (n + 1) →₀ ℕ)) : ℕ := ∑ u ∈ A, wt c u

theorem mv_apply (u : Fin (n + 1) →₀ ℕ) (j : ℕ) (l : Fin (n + 1)) :
    mv i c u j l = if l = i then j else if l = c then u i + u c - j else u l := rfl

@[scoped simp] theorem mv_apply_i (u : Fin (n + 1) →₀ ℕ) (j : ℕ) : mv i c u j i = j := by simp [mv_apply]

theorem mem_J {A : Finset (Fin (n + 1) →₀ ℕ)} {m : Fin (n + 1) →₀ ℕ} {j : ℕ} :
    j ∈ J i c A m ↔ j ≤ m c ∧ mv i c m j ∈ A := by
  simp [J]

theorem card_J_le (A : Finset (Fin (n + 1) →₀ ℕ)) (m : Fin (n + 1) →₀ ℕ) : (J i c A m).card ≤ m c + 1 :=
  (Finset.card_filter_le _ _).trans (by simp)

theorem J_mono {A A' : Finset (Fin (n + 1) →₀ ℕ)} (h : A ⊆ A') (m : Fin (n + 1) →₀ ℕ) :
    J i c A m ⊆ J i c A' m := fun j hj => by
  rw [mem_J] at hj ⊢; exact ⟨hj.1, h hj.2⟩

theorem mv_injective (u : Fin (n + 1) →₀ ℕ) : Function.Injective (mv i c u) := fun j j' h => by
  have := congrArg (fun f => f i) h
  simpa using this

variable {i c} (hic : i ≠ c)
include hic

theorem mv_apply_c (u : Fin (n + 1) →₀ ℕ) (j : ℕ) : mv i c u j c = u i + u c - j := by
  simp [mv_apply, Ne.symm hic]

omit hic in
theorem mv_apply_ne {l : Fin (n + 1)} (hli : l ≠ i) (hlc : l ≠ c) (u : Fin (n + 1) →₀ ℕ) (j : ℕ) :
    mv i c u j l = u l := by
  simp [mv_apply, hli, hlc]

omit hic in
@[scoped simp] theorem key_apply_i (u : Fin (n + 1) →₀ ℕ) : key i c u i = 0 := by simp [key]

theorem key_apply_c (u : Fin (n + 1) →₀ ℕ) : key i c u c = u i + u c := by
  simp [key, mv_apply_c hic]

omit hic in
theorem key_apply_ne {l : Fin (n + 1)} (hli : l ≠ i) (hlc : l ≠ c) (u : Fin (n + 1) →₀ ℕ) :
    key i c u l = u l := mv_apply_ne hli hlc u 0

omit hic in

theorem ext3 {f g : Fin (n + 1) →₀ ℕ} (hi : f i = g i) (hc : f c = g c)
    (h : ∀ l, l ≠ i → l ≠ c → f l = g l) : f = g := by
  ext l
  by_cases hli : l = i
  · rw [hli]; exact hi
  by_cases hlc : l = c
  · rw [hlc]; exact hc
  exact h l hli hlc

theorem mv_key (u : Fin (n + 1) →₀ ℕ) (j : ℕ) : mv i c (key i c u) j = mv i c u j :=
  ext3 (i := i) (c := c) (by simp) (by rw [mv_apply_c hic, mv_apply_c hic, key_apply_i, key_apply_c hic]; omega)
    fun l hli hlc => by rw [mv_apply_ne hli hlc, mv_apply_ne hli hlc, key_apply_ne hli hlc]

theorem key_mv (u : Fin (n + 1) →₀ ℕ) (j : ℕ) (hj : j ≤ u i + u c) : key i c (mv i c u j) = key i c u :=
  ext3 (i := i) (c := c) (by simp) (by rw [key_apply_c hic, key_apply_c hic, mv_apply_i, mv_apply_c hic]; omega)
    fun l hli hlc => by rw [key_apply_ne hli hlc, key_apply_ne hli hlc, mv_apply_ne hli hlc]

theorem key_key (u : Fin (n + 1) →₀ ℕ) : key i c (key i c u) = key i c u := key_mv hic u 0 (Nat.zero_le _)

theorem mv_self (u : Fin (n + 1) →₀ ℕ) : mv i c u (u i) = u :=
  ext3 (i := i) (c := c) (by simp) (by rw [mv_apply_c hic]; omega) fun l hli hlc => mv_apply_ne hli hlc u _

theorem sub_add_eq_mv (u : Fin (n + 1) →₀ ℕ) (hu : 1 ≤ u i) :
    u - Finsupp.single i 1 + Finsupp.single c 1 = mv i c (key i c u) (u i - 1) :=
  ext3 (i := i) (c := c) (by simp [hic])
    (by rw [mv_apply_c hic, key_apply_i, key_apply_c hic]
        simp [Ne.symm hic]; omega)
    fun l hli hlc => by
      rw [mv_apply_ne hli hlc, key_apply_ne hli hlc]
      simp [Ne.symm hli, Ne.symm hlc]

theorem mv_sub_single_i (u : Fin (n + 1) →₀ ℕ) (x : ℕ) (hx : 1 ≤ x) (hu : 1 ≤ u i) :
    mv i c u x - Finsupp.single i 1 = mv i c (u - Finsupp.single i 1) (x - 1) :=
  ext3 (i := i) (c := c) (by simp) (by rw [Finsupp.tsub_apply, mv_apply_c hic, mv_apply_c hic]; simp [Ne.symm hic]; omega)
    fun l hli hlc => by
      rw [Finsupp.tsub_apply, mv_apply_ne hli hlc, mv_apply_ne hli hlc, Finsupp.tsub_apply]

theorem mv_sub_single_i' (u : Fin (n + 1) →₀ ℕ) (x : ℕ) (hx : 1 ≤ x) (hu : 1 ≤ u c) :
    mv i c u x - Finsupp.single i 1 = mv i c (u - Finsupp.single c 1) (x - 1) :=
  ext3 (i := i) (c := c) (by simp) (by rw [Finsupp.tsub_apply, mv_apply_c hic, mv_apply_c hic]; simp [hic, Ne.symm hic]; omega)
    fun l hli hlc => by
      rw [Finsupp.tsub_apply, mv_apply_ne hli hlc, mv_apply_ne hli hlc, Finsupp.tsub_apply]
      simp [Ne.symm hli, Ne.symm hlc]

theorem mv_sub_single_c (u : Fin (n + 1) →₀ ℕ) (x : ℕ) (hu : 1 ≤ u c) :
    mv i c u x - Finsupp.single c 1 = mv i c (u - Finsupp.single c 1) x :=
  ext3 (i := i) (c := c) (by simp [Ne.symm hic])
    (by rw [Finsupp.tsub_apply, mv_apply_c hic, mv_apply_c hic]; simp [hic]; omega)
    fun l hli hlc => by
      rw [Finsupp.tsub_apply, mv_apply_ne hli hlc, mv_apply_ne hli hlc, Finsupp.tsub_apply]

theorem mv_sub_single_ne {l : Fin (n + 1)} (hli : l ≠ i) (hlc : l ≠ c) (u : Fin (n + 1) →₀ ℕ) (x : ℕ) :
    mv i c u x - Finsupp.single l 1 = mv i c (u - Finsupp.single l 1) x :=
  ext3 (i := i) (c := c) (by simp [hli])
    (by rw [Finsupp.tsub_apply, mv_apply_c hic, mv_apply_c hic]; simp [hli, hlc])
    fun l' hl'i hl'c => by
      rw [Finsupp.tsub_apply, mv_apply_ne hl'i hl'c, mv_apply_ne hl'i hl'c, Finsupp.tsub_apply]

theorem mem_comp_iff (A : Finset (Fin (n + 1) →₀ ℕ)) (u : Fin (n + 1) →₀ ℕ) :
    u ∈ comp i c A ↔ u i < (J i c A (key i c u)).card := by
  constructor
  · intro hu
    simp only [comp, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range] at hu
    obtain ⟨m, ⟨a, -, rfl⟩, j, hj, rfl⟩ := hu
    have hjle : j ≤ a i + a c := by
      have := card_J_le i c A (key i c a); rw [key_apply_c hic] at this; omega
    rw [mv_apply_i, mv_key hic, key_mv hic a j hjle]
    exact hj
  · intro hu
    simp only [comp, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range]
    obtain ⟨j', hj'⟩ := Finset.card_pos.1 (show 0 < (J i c A (key i c u)).card by omega)
    rw [mem_J, key_apply_c hic, mv_key hic] at hj'
    refine ⟨key i c u, ⟨mv i c u j', hj'.2, key_mv hic u j' hj'.1⟩, u i, hu, ?_⟩
    rw [mv_key hic, mv_self hic]

theorem comp_mono {A A' : Finset (Fin (n + 1) →₀ ℕ)} (h : A ⊆ A') : comp i c A ⊆ comp i c A' :=
  fun u hu => by
    rw [mem_comp_iff hic] at hu ⊢
    exact hu.trans_le (Finset.card_le_card (J_mono i c h _))

theorem comp_step_mem {A : Finset (Fin (n + 1) →₀ ℕ)} {u : Fin (n + 1) →₀ ℕ} (hu : u ∈ comp i c A)
    (h1 : 1 ≤ u i) : u - Finsupp.single i 1 + Finsupp.single c 1 ∈ comp i c A := by
  rw [mem_comp_iff hic] at hu
  rw [sub_add_eq_mv hic u h1, mem_comp_iff hic, mv_apply_i, mv_key hic, key_mv hic u _ (by omega)]
  omega

theorem sum_biUnion_mv (K : Finset (Fin (n + 1) →₀ ℕ)) (hK : ∀ m ∈ K, key i c m = m)
    (S : (Fin (n + 1) →₀ ℕ) → Finset ℕ) (hS : ∀ m ∈ K, ∀ j ∈ S m, j ≤ m i + m c)
    (f : (Fin (n + 1) →₀ ℕ) → ℕ) :
    ∑ u ∈ K.biUnion (fun m => (S m).image (mv i c m)), f u = ∑ m ∈ K, ∑ j ∈ S m, f (mv i c m j) := by
  rw [Finset.sum_biUnion]
  · exact Finset.sum_congr rfl fun m _ => Finset.sum_image fun j _ j' _ h => mv_injective i c m h
  · intro m hm m' hm' hne
    show Disjoint _ _
    rw [Finset.disjoint_left]
    intro u hu hu'
    rw [Finset.mem_image] at hu hu'
    obtain ⟨j, hj, rfl⟩ := hu
    obtain ⟨j', hj', h⟩ := hu'
    apply hne
    have h1 := key_mv hic m j (hS m hm j hj)
    have h2 := key_mv hic m' j' (hS m' hm' j' hj')
    rw [h, h1, hK m hm] at h2
    rw [hK m' hm'] at h2
    exact h2

theorem key_of_mem_image {A : Finset (Fin (n + 1) →₀ ℕ)} {m : Fin (n + 1) →₀ ℕ}
    (hm : m ∈ A.image (key i c)) : key i c m = m := by
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hm; exact key_key hic a

theorem sum_eq_sum_key (A : Finset (Fin (n + 1) →₀ ℕ)) (f : (Fin (n + 1) →₀ ℕ) → ℕ) :
    ∑ u ∈ A, f u = ∑ m ∈ A.image (key i c), ∑ j ∈ J i c A m, f (mv i c m j) := by
  have hA : A = (A.image (key i c)).biUnion (fun m => (J i c A m).image (mv i c m)) := by
    ext u
    simp only [Finset.mem_biUnion, Finset.mem_image]
    constructor
    · intro hu
      refine ⟨key i c u, ⟨u, hu, rfl⟩, u i, ?_, by rw [mv_key hic, mv_self hic]⟩
      rw [mem_J, key_apply_c hic, mv_key hic, mv_self hic]; exact ⟨by omega, hu⟩
    · rintro ⟨m, -, j, hj, rfl⟩
      exact ((mem_J i c).1 hj).2
  conv_lhs => rw [hA]
  refine sum_biUnion_mv hic _ (fun m hm => key_of_mem_image hic hm) _ (fun m hm j hj => ?_) f
  have := ((mem_J i c).1 hj).1; omega

theorem sum_comp (A : Finset (Fin (n + 1) →₀ ℕ)) (f : (Fin (n + 1) →₀ ℕ) → ℕ) :
    ∑ u ∈ comp i c A, f u = ∑ m ∈ A.image (key i c), ∑ j ∈ Finset.range (J i c A m).card, f (mv i c m j) := by
  refine sum_biUnion_mv hic _ (fun m hm => key_of_mem_image hic hm) _ (fun m hm j hj => ?_) f
  rw [Finset.mem_range] at hj
  have := card_J_le i c A m; omega

theorem card_comp (A : Finset (Fin (n + 1) →₀ ℕ)) : (comp i c A).card = A.card := by
  rw [Finset.card_eq_sum_ones, Finset.card_eq_sum_ones, sum_comp hic, sum_eq_sum_key hic A]
  simp

theorem degree_mv (u : Fin (n + 1) →₀ ℕ) (j : ℕ) (hj : j ≤ u i + u c) : (mv i c u j).degree = u.degree := by
  have hi := Finset.mem_univ i
  have hc' : c ∈ Finset.univ.erase i := Finset.mem_erase.2 ⟨Ne.symm hic, Finset.mem_univ c⟩
  rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum,
    ← Finset.add_sum_erase Finset.univ (fun l => mv i c u j l) hi,
    ← Finset.add_sum_erase Finset.univ (fun l => u l) hi,
    ← Finset.add_sum_erase _ (fun l => mv i c u j l) hc',
    ← Finset.add_sum_erase _ (fun l => u l) hc', mv_apply_i, mv_apply_c hic]
  have : ∑ x ∈ (Finset.univ.erase i).erase c, mv i c u j x = ∑ x ∈ (Finset.univ.erase i).erase c, u x :=
    Finset.sum_congr rfl fun l hl => by
      simp only [Finset.mem_erase] at hl
      exact mv_apply_ne hl.2.1 hl.1 u j
  rw [this]; omega

theorem mv_mem_MonW {u : Fin (n + 1) →₀ ℕ} {W e : ℕ} (hu : u ∈ MonW n W e) (hiW : (i : ℕ) < W)
    (hcW : (c : ℕ) < W) {j : ℕ} (hj : j ≤ u i + u c) : mv i c u j ∈ MonW n W e := by
  rw [mem_MonW] at hu ⊢
  refine ⟨by rw [degree_mv hic u j hj]; exact hu.1, fun l hl => ?_⟩
  have hli : l ≠ i := fun h => by rw [h] at hl; omega
  have hlc : l ≠ c := fun h => by rw [h] at hl; omega
  rw [mv_apply_ne hli hlc]; exact hu.2 l hl

theorem comp_subset_MonW {A : Finset (Fin (n + 1) →₀ ℕ)} {W e : ℕ} (hA : A ⊆ MonW n W e)
    (hiW : (i : ℕ) < W) (hcW : (c : ℕ) < W) : comp i c A ⊆ MonW n W e := by
  intro u hu
  simp only [comp, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range] at hu
  obtain ⟨m, ⟨a, ha, rfl⟩, j, hj, rfl⟩ := hu
  rw [mv_key hic]
  have hjle : j ≤ a i + a c := by
    have := card_J_le i c A (key i c a); rw [key_apply_c hic] at this; omega
  exact mv_mem_MonW hic (hA ha) hiW hcW hjle

omit hic in

theorem sum_range_card_le (S : Finset ℕ) :
    ∑ j ∈ Finset.range S.card, j ≤ ∑ j ∈ S, j ∧
      (∑ j ∈ Finset.range S.card, j = ∑ j ∈ S, j → S = Finset.range S.card) := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a s has ih =>
    have ha : a ∉ s := fun h => lt_irrefl a (has a h)
    have hcard : s.card ≤ a := by
      have : s ⊆ Finset.range a := fun x hx => Finset.mem_range.2 (has x hx)
      simpa using Finset.card_le_card this
    rw [Finset.card_insert_of_notMem ha, Finset.sum_range_succ, Finset.sum_insert ha]
    refine ⟨by omega, fun h => ?_⟩
    have h1 : ∑ j ∈ Finset.range s.card, j = ∑ j ∈ s, j := by omega
    have h2 : s.card = a := by omega
    have h3 := ih.2 h1
    rw [Finset.range_add_one, ← h3, h2]

omit hic in

theorem min_card_le (S S' : Finset ℕ) (t : ℕ) (h1 : ∀ x ∈ S, x < t → x ∈ S')
    (h2 : ∀ x ∈ S, 1 ≤ x → x - 1 ∈ S') : min S.card t ≤ S'.card := by
  by_cases hfull : ∀ g, g ≤ t → g ∈ S
  · have : Finset.range t ⊆ S' := fun x hx => by
      rw [Finset.mem_range] at hx; exact h1 x (hfull x hx.le) hx
    have := Finset.card_le_card this
    rw [Finset.card_range] at this
    omega
  · push Not at hfull
    obtain ⟨g, hgt, hgS⟩ := hfull
    have : S.card ≤ S'.card := by
      refine Finset.card_le_card_of_injOn (fun x => if x < g then x else x - 1) (fun x hx => ?_) ?_
      · rw [Finset.mem_coe] at hx
        have hxg : x ≠ g := fun h => hgS (h ▸ hx)
        show (if x < g then x else x - 1) ∈ (S' : Set ℕ)
        rw [Finset.mem_coe]
        split_ifs with h
        · exact h1 x hx (by omega)
        · exact h2 x hx (by omega)
      · intro x hx y hy hxy
        rw [Finset.mem_coe] at hx hy
        have hxg : x ≠ g := fun h => hgS (h ▸ hx)
        have hyg : y ≠ g := fun h => hgS (h ▸ hy)
        simp only at hxy
        split_ifs at hxy <;> omega
    omega

theorem sub_single_mem_comp {A D : Finset (Fin (n + 1) →₀ ℕ)}
    (hAD : ∀ a ∈ A, ∀ l : Fin (n + 1), 1 ≤ a l → a - Finsupp.single l 1 ∈ D)
    {u : Fin (n + 1) →₀ ℕ} (hu : u ∈ comp i c A) (l : Fin (n + 1)) (hl : 1 ≤ u l) :
    u - Finsupp.single l 1 ∈ comp i c D := by
  rw [mem_comp_iff hic] at hu ⊢
  have hmem : ∀ x ∈ J i c A (key i c u), x ≤ u i + u c ∧ mv i c u x ∈ A := fun x hx => by
    have := (mem_J i c).1 hx; rw [key_apply_c hic, mv_key hic] at this; exact this
  by_cases hli : l = i
  · subst hli
    have e1 : (u - Finsupp.single l 1 : Fin (n + 1) →₀ ℕ) l = u l - 1 := by simp
    rw [e1]
    have hinj : ((J l c A (key l c u)).erase 0).card ≤ (J l c D (key l c (u - Finsupp.single l 1))).card := by
      refine Finset.card_le_card_of_injOn (fun x => x - 1) (fun x hx => ?_) ?_
      · rw [Finset.coe_erase, Set.mem_diff, Finset.mem_coe, Set.mem_singleton_iff] at hx
        obtain ⟨hx, hx0⟩ := hx
        obtain ⟨hxle, hxA⟩ := hmem x hx
        rw [Finset.mem_coe, mem_J, key_apply_c hic, mv_key hic]
        refine ⟨by rw [Finsupp.tsub_apply, Finsupp.tsub_apply]; simp [hic]; omega, ?_⟩
        have := hAD _ hxA l (by rw [mv_apply_i]; omega)
        rwa [mv_sub_single_i hic u x (by omega) hl] at this
      · intro x hx y hy hxy
        rw [Finset.coe_erase, Set.mem_diff, Finset.mem_coe, Set.mem_singleton_iff] at hx hy
        simp only at hxy
        omega
    have := Finset.pred_card_le_card_erase (s := J l c A (key l c u)) (a := 0)
    omega
  by_cases hlc : l = c
  · subst hlc
    have e1 : (u - Finsupp.single l 1 : Fin (n + 1) →₀ ℕ) i = u i := by simp [hic]
    rw [e1]
    have key_le : min (J i l A (key i l u)).card (u i + u l) ≤ (J i l D (key i l (u - Finsupp.single l 1))).card := by
      refine min_card_le _ _ (u i + u l) (fun x hx hxt => ?_) (fun x hx hx1 => ?_)
      · obtain ⟨-, hxA⟩ := hmem x hx
        rw [mem_J, key_apply_c hic, mv_key hic]
        refine ⟨by rw [Finsupp.tsub_apply, Finsupp.tsub_apply]; simp [Ne.symm hic]; omega, ?_⟩
        have := hAD _ hxA l (by rw [mv_apply_c hic]; omega)
        rwa [mv_sub_single_c hic u x hl] at this
      · obtain ⟨hxle, hxA⟩ := hmem x hx
        rw [mem_J, key_apply_c hic, mv_key hic]
        refine ⟨by rw [Finsupp.tsub_apply, Finsupp.tsub_apply]; simp [Ne.symm hic]; omega, ?_⟩
        have := hAD _ hxA i (by rw [mv_apply_i]; omega)
        rwa [mv_sub_single_i' hic u x hx1 hl] at this
    have : u i < u i + u l := by omega
    omega
  · have e1 : (u - Finsupp.single l 1 : Fin (n + 1) →₀ ℕ) i = u i := by simp [hli]
    rw [e1]
    have : (J i c A (key i c u)).card ≤ (J i c D (key i c (u - Finsupp.single l 1))).card := by
      refine Finset.card_le_card fun x hx => ?_
      obtain ⟨hxle, hxA⟩ := hmem x hx
      rw [mem_J, key_apply_c hic, mv_key hic]
      refine ⟨by rw [Finsupp.tsub_apply, Finsupp.tsub_apply]; simp [hli, hlc]; omega, ?_⟩
      have := hAD _ hxA l (by rw [mv_apply_ne hli hlc]; exact hl)
      rwa [mv_sub_single_ne hic hli hlc u x] at this
    omega

theorem card_Bplus_le_comp (W e : ℕ) (X : Finset (Fin (n + 1) →₀ ℕ)) (hiW : (i : ℕ) < W)
    (hcW : (c : ℕ) < W) : (Bplus n W e X).card ≤ (Bplus n W e (comp i c X)).card := by
  rw [← card_comp hic (Bplus n W e X)]
  refine Finset.card_le_card fun u hu => ?_
  rw [mem_Bplus]
  refine ⟨comp_subset_MonW hic (Bplus_subset_MonW n W e X) hiW hcW hu, fun l hl => ?_⟩
  exact sub_single_mem_comp hic (fun a ha l hl => ((mem_Bplus n W e X a).1 ha).2 l hl) hu l hl

theorem wt_mv (m : Fin (n + 1) →₀ ℕ) (j : ℕ) (hm : m i = 0) : wt c (mv i c m j) = wt c m + j := by
  unfold wt
  have hi : i ∈ Finset.univ.erase c := Finset.mem_erase.2 ⟨hic, Finset.mem_univ _⟩
  rw [← Finset.add_sum_erase _ (fun l => mv i c m j l) hi, ← Finset.add_sum_erase _ (fun l => m l) hi,
    mv_apply_i, hm, zero_add, add_comm]
  congr 1
  exact Finset.sum_congr rfl fun l hl => by
    simp only [Finset.mem_erase] at hl
    exact mv_apply_ne hl.1 hl.2.1 _ _

theorem pot_comp_lt (A : Finset (Fin (n + 1) →₀ ℕ)) {u : Fin (n + 1) →₀ ℕ} (hu : u ∈ A) (h1 : 1 ≤ u i)
    (hnot : u - Finsupp.single i 1 + Finsupp.single c 1 ∉ A) : pot c (comp i c A) < pot c A := by
  unfold pot
  rw [sum_comp hic, sum_eq_sum_key hic A]
  have hrw : ∀ m ∈ A.image (key i c), ∀ (S : Finset ℕ),
      ∑ j ∈ S, wt c (mv i c m j) = S.card * wt c m + ∑ j ∈ S, j := fun m hm S => by
    have hm0 : m i = 0 := by have := key_apply_i (i := i) (c := c) m; rwa [key_of_mem_image hic hm] at this
    rw [Finset.sum_congr rfl fun j _ => wt_mv hic m j hm0, Finset.sum_add_distrib, Finset.sum_const,
      smul_eq_mul]
  apply Finset.sum_lt_sum
  · intro m hm
    rw [hrw m hm, hrw m hm, Finset.card_range]
    have := (sum_range_card_le (J i c A m)).1
    omega
  · refine ⟨key i c u, Finset.mem_image_of_mem _ hu, ?_⟩
    have hm := Finset.mem_image_of_mem (key i c) hu
    rw [hrw _ hm, hrw _ hm, Finset.card_range]
    have hle := (sum_range_card_le (J i c A (key i c u))).1
    have hne : J i c A (key i c u) ≠ Finset.range (J i c A (key i c u)).card := by
      intro heq
      have hin : u i ∈ J i c A (key i c u) :=
        (mem_J i c).2 ⟨by rw [key_apply_c hic]; omega, by rw [mv_key hic, mv_self hic]; exact hu⟩
      have hout : u i - 1 ∉ J i c A (key i c u) := fun h =>
        hnot (by rw [sub_add_eq_mv hic u h1]; exact ((mem_J i c).1 h).2)
      rw [heq, Finset.mem_range] at hin hout
      omega
    have hlt : ∑ j ∈ Finset.range (J i c A (key i c u)).card, j < ∑ j ∈ J i c A (key i c u), j :=
      lt_of_le_of_ne hle fun h => hne ((sum_range_card_le _).2 h)
    omega

end Compression

theorem exists_stable (w : ℕ) (c : Fin (n + 1)) (hcw : (c : ℕ) = w) (e : ℕ) :
    ∀ (P : ℕ) (X : Finset (Fin (n + 1) →₀ ℕ)), pot c X = P → X ⊆ MonW n (w + 1) e →
    ∃ Y : Finset (Fin (n + 1) →₀ ℕ), Y ⊆ MonW n (w + 1) e ∧ Y.card = X.card ∧
      (Bplus n (w + 1) e X).card ≤ (Bplus n (w + 1) e Y).card ∧
      ∀ u ∈ Y, ∀ l : Fin (n + 1), (l : ℕ) < w → 1 ≤ u l →
        u - Finsupp.single l 1 + Finsupp.single c 1 ∈ Y := by
  intro P
  induction P using Nat.strong_induction_on with
  | _ P IH =>
  intro X hP hX
  by_cases hst : ∀ u ∈ X, ∀ l : Fin (n + 1), (l : ℕ) < w → 1 ≤ u l →
      u - Finsupp.single l 1 + Finsupp.single c 1 ∈ X
  · exact ⟨X, hX, rfl, le_rfl, hst⟩
  · push Not at hst
    obtain ⟨u, hu, l, hlw, hul, hnot⟩ := hst
    have hlc : l ≠ c := fun h => by rw [h, hcw] at hlw; omega
    have hlt : pot c (comp l c X) < P := hP ▸ pot_comp_lt hlc X hu hul hnot
    obtain ⟨Y, hY, hYc, hYB, hYs⟩ :=
      IH _ hlt (comp l c X) rfl (comp_subset_MonW hlc hX (by omega) (by omega))
    exact ⟨Y, hY, hYc.trans (card_comp hlc X), (card_Bplus_le_comp hlc _ e X (by omega) (by omega)).trans hYB,
      hYs⟩

variable (n)

noncomputable def T (w : ℕ) (c : Fin (n + 1)) (X : Finset (Fin (n + 1) →₀ ℕ)) (e k : ℕ) :
    Finset (Fin (n + 1) →₀ ℕ) :=
  (MonW n w (e - k)).filter fun v => v + Finsupp.single c k ∈ X

theorem T_subset (w : ℕ) (c : Fin (n + 1)) (X : Finset (Fin (n + 1) →₀ ℕ)) (e k : ℕ) :
    T n w c X e k ⊆ MonW n w (e - k) := Finset.filter_subset _ _

variable {n}

section Tower

variable {w : ℕ} {c : Fin (n + 1)} (hcw : (c : ℕ) = w) {X : Finset (Fin (n + 1) →₀ ℕ)} {e : ℕ}
  (hX : X ⊆ MonW n (w + 1) e)
include hcw hX

theorem mem_T_iff {k : ℕ} (hk : k ≤ e) (v : Fin (n + 1) →₀ ℕ) :
    v ∈ T n w c X e k ↔ v c = 0 ∧ v + Finsupp.single c k ∈ X := by
  rw [T, Finset.mem_filter, mem_MonW]
  constructor
  · rintro ⟨⟨-, hsupp⟩, hmem⟩; exact ⟨hsupp c (by omega), hmem⟩
  · rintro ⟨hc0, hmem⟩
    have hu := (mem_MonW n _ _ _).1 (hX hmem)
    refine ⟨⟨?_, fun l hl => ?_⟩, hmem⟩
    · have := hu.1; rw [map_add, Finsupp.degree_single] at this; omega
    · by_cases hlc : l = c
      · rw [hlc]; exact hc0
      · have hl' : w + 1 ≤ (l : ℕ) := by
          have : (l : ℕ) ≠ w := fun h => hlc (Fin.ext (h.trans hcw.symm)); omega
        have := hu.2 l hl'
        rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hlc)] at this; omega

theorem card_T {k : ℕ} (hk : k ≤ e) : (T n w c X e k).card = (X.filter fun u => u c = k).card := by
  refine Finset.card_bij' (fun v _ => v + Finsupp.single c k) (fun u _ => u - Finsupp.single c k)
    ?_ ?_ ?_ ?_
  · intro v hv
    rw [mem_T_iff hcw hX hk] at hv
    rw [Finset.mem_filter]
    exact ⟨hv.2, by rw [Finsupp.add_apply, Finsupp.single_eq_same, hv.1, zero_add]⟩
  · intro u hu
    rw [Finset.mem_filter] at hu
    rw [mem_T_iff hcw hX hk]
    refine ⟨by rw [Finsupp.tsub_apply, Finsupp.single_eq_same, hu.2, Nat.sub_self], ?_⟩
    rw [tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (by rw [hu.2]))]
    exact hu.1
  · intro v _; exact add_tsub_cancel_right _ _
  · intro u hu
    rw [Finset.mem_filter] at hu
    exact tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (by rw [hu.2]))

theorem sum_card_T : ∑ k ∈ Finset.range (e + 1), (T n w c X e k).card = X.card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun u => u c) (s := X) (t := Finset.range (e + 1))
    (fun u hu => by
      rw [Finset.mem_coe] at hu
      rw [Finset.mem_coe, Finset.mem_range, Nat.lt_succ_iff, ← ((mem_MonW n _ _ _).1 (hX hu)).1]
      exact Finsupp.le_degree c u)]
  exact Finset.sum_congr rfl fun k hk => card_T hcw hX (by rw [Finset.mem_range] at hk; omega)

theorem card_Bplus_succ_le : (Bplus n (w + 1) e X).card ≤ (Bplus n w e (T n w c X e 0)).card + X.card := by
  classical
  have hsub : Bplus n (w + 1) e X ⊆ Bplus n w e (T n w c X e 0) ∪ X.image (· + Finsupp.single c 1) := by
    intro u hu
    rw [mem_Bplus, mem_MonW] at hu
    obtain ⟨⟨hdeg, hsupp⟩, hdiv⟩ := hu
    rw [Finset.mem_union]
    by_cases h0 : u c = 0
    · left
      rw [mem_Bplus, mem_MonW]
      refine ⟨⟨hdeg, fun l hl => ?_⟩, fun l hl => ?_⟩
      · by_cases hlc : l = c
        · rw [hlc]; exact h0
        · exact hsupp l (by have : (l : ℕ) ≠ w := fun h => hlc (Fin.ext (h.trans hcw.symm)); omega)
      · rw [mem_T_iff hcw hX (Nat.zero_le e), Finsupp.single_zero, add_zero]
        exact ⟨by rw [Finsupp.tsub_apply, h0, Nat.zero_sub], hdiv l hl⟩
    · right
      rw [Finset.mem_image]
      exact ⟨u - Finsupp.single c 1, hdiv c (by omega), Finsupp.sub_add_single_one_cancel h0⟩
  calc (Bplus n (w + 1) e X).card ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ _ := Nat.add_le_add_left Finset.card_image_le _

omit hcw hX in
theorem sub_add_single_comm (v : Fin (n + 1) →₀ ℕ) {l c' : Fin (n + 1)} (hlc : l ≠ c') (k : ℕ) :
    v - Finsupp.single l 1 + Finsupp.single c' (k + 1) =
      v + Finsupp.single c' k - Finsupp.single l 1 + Finsupp.single c' 1 := by
  ext x
  simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]
  rcases eq_or_ne l x with rfl | h1
  · simp [Ne.symm hlc]
  · rcases eq_or_ne c' x with rfl | h2
    · simp [h1, add_assoc]
    · simp [h1, h2]

theorem T_subset_Bplus
    (hstab : ∀ u ∈ X, ∀ l : Fin (n + 1), (l : ℕ) < w → 1 ≤ u l →
      u - Finsupp.single l 1 + Finsupp.single c 1 ∈ X)
    (k : ℕ) (hk : k + 1 ≤ e) : T n w c X e k ⊆ Bplus n w (e - (k + 1)) (T n w c X e (k + 1)) := by
  intro v hv
  have hv' := (mem_T_iff hcw hX (by omega) v).1 hv
  have hvM := (mem_MonW n _ _ _).1 (T_subset n w c X e k hv)
  rw [mem_Bplus, show e - (k + 1) + 1 = e - k by omega, mem_MonW]
  refine ⟨hvM, fun l hl => ?_⟩
  have hlw : (l : ℕ) < w := by
    by_contra h
    push Not at h
    have := hvM.2 l h; omega
  have hlc : l ≠ c := fun h => by rw [h, hcw] at hlw; omega
  rw [mem_T_iff hcw hX hk]
  refine ⟨by rw [Finsupp.tsub_apply, hv'.1, Nat.zero_sub], ?_⟩
  have := hstab _ hv'.2 l hlw
    (by rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hlc)]; omega)
  rwa [← sub_add_single_comm v hlc k] at this

omit hcw hX in
theorem card_T_last_le : (T n w c X e e).card ≤ 1 := by
  refine (Finset.card_le_card (T_subset n w c X e e)).trans ?_
  rw [Nat.sub_self, MonW_zero_right, Finset.card_singleton]

theorem card_T_last_eq
    (hstab : ∀ u ∈ X, ∀ l : Fin (n + 1), (l : ℕ) < w → 1 ≤ u l →
      u - Finsupp.single l 1 + Finsupp.single c 1 ∈ X)
    (he : 1 ≤ e) (hne : 1 ≤ (T n w c X e (e - 1)).card) : (T n w c X e e).card = 1 := by
  refine le_antisymm card_T_last_le ?_
  obtain ⟨v, hv⟩ := Finset.card_pos.1 (show 0 < (T n w c X e (e - 1)).card by omega)
  have hsub := T_subset_Bplus hcw hX hstab (e - 1) (by omega) hv
  rw [show e - 1 + 1 = e by omega, mem_Bplus] at hsub
  have hdeg := ((mem_MonW n _ _ _).1 (T_subset n w c X e (e - 1) hv)).1
  obtain ⟨l, hl⟩ := exists_one_le_of_degree_ne_zero v (by rw [hdeg]; omega)
  exact Finset.card_pos.2 ⟨_, hsub.2 l hl⟩

end Tower

theorem stable_bound (w : ℕ) (c : Fin (n + 1)) (hcw : (c : ℕ) = w)
    (ih : ∀ e, 1 ≤ e → ∀ Z : Finset (Fin (n + 1) →₀ ℕ), Z ⊆ MonW n w e →
      (Bplus n w e Z).card ≤ Nat.macaulayPow e Z.card)
    {e : ℕ} (he : 1 ≤ e) {X : Finset (Fin (n + 1) →₀ ℕ)} (hX : X ⊆ MonW n (w + 1) e)
    (hstab : ∀ u ∈ X, ∀ l : Fin (n + 1), (l : ℕ) < w → 1 ≤ u l →
      u - Finsupp.single l 1 + Finsupp.single c 1 ∈ X) :
    (Bplus n (w + 1) e X).card ≤ Nat.macaulayPow e X.card := by
  obtain ⟨e, rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  have hsum : ∑ k ∈ Finset.range (e + 2), (T n w c X (e + 1) k).card = X.card := sum_card_T hcw hX
  have h := tower_bound e (fun k => (T n w c X (e + 1) k).card) (Bplus n w (e + 1) (T n w c X (e + 1) 0)).card
    card_T_last_le ?_ ?_ ?_
  · rw [hsum] at h
    exact (card_Bplus_succ_le hcw hX).trans h
  · intro h1
    exact card_T_last_eq hcw hX hstab (by omega) (by simpa using h1)
  · intro k hk
    have hsub := T_subset_Bplus hcw hX hstab k (by omega)
    rw [show e + 1 - (k + 1) = e - k by omega] at hsub
    refine (Finset.card_le_card hsub).trans (ih (e - k) (by omega) _ ?_)
    have := T_subset n w c X (e + 1) (k + 1)
    rwa [show e + 1 - (k + 1) = e - k by omega] at this
  · exact ih (e + 1) (by omega) _ (T_subset n w c X (e + 1) 0)

theorem main : ∀ w : ℕ, w ≤ n + 1 → ∀ e : ℕ, 1 ≤ e → ∀ X : Finset (Fin (n + 1) →₀ ℕ),
    X ⊆ MonW n w e → (Bplus n w e X).card ≤ Nat.macaulayPow e X.card
  | 0, _, e, he, X, hX => by
      obtain ⟨e, rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
      have h1 : X = ∅ := Finset.subset_empty.1 (by rw [MonW_zero_succ] at hX; exact hX)
      subst h1
      have h2 : Bplus n 0 (e + 1) ∅ = ∅ := Finset.subset_empty.1 (by
        have := Bplus_subset_MonW n 0 (e + 1) ∅; rw [MonW_zero_succ] at this; exact this)
      rw [h2, Finset.card_empty]; exact Nat.zero_le _
  | w + 1, hw, e, he, X, hX => by
      obtain ⟨Y, hY, hYc, hYB, hYs⟩ := exists_stable w ⟨w, by omega⟩ rfl e _ X rfl hX
      refine hYB.trans ?_
      rw [← hYc]
      exact stable_bound w ⟨w, by omega⟩ rfl (main w (by omega)) he hY hYs

end MacaulayCL
p2m_reactivate "P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL"

open MacaulayCL in
theorem solution
    (n d : ℕ) (hd : 1 ≤ d) (B : Finset (Fin (n + 1) →₀ ℕ)) (hB : ∀ m ∈ B, m.degree = d)
    (C : Finset (Fin (n + 1) →₀ ℕ)) (hC : ∀ u ∈ C, u.degree = d + 1)
    (hCB : ∀ u ∈ C, ∀ i : Fin (n + 1), 1 ≤ u i → u - Finsupp.single i 1 ∈ B) :
    C.card ≤ Nat.macaulayPow d B.card := by
  have hBW : B ⊆ MonW n (n + 1) d := fun m hm =>
    (mem_MonW n _ _ m).2 ⟨hB m hm, fun i hi => absurd i.2 (by omega)⟩
  have hCsub : C ⊆ Bplus n (n + 1) d B := fun u hu =>
    (mem_Bplus n _ _ B u).2 ⟨(mem_MonW n _ _ u).2 ⟨hC u hu, fun i hi => absurd i.2 (by omega)⟩, hCB u hu⟩
  exact (Finset.card_le_card hCsub).trans (main (n + 1) le_rfl d hd B hBW)

end S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem
end P2MW
export P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem (solution)
