-- Prove2me | solution 1 for FedergruenTzur.MinPred.theorem1c_iii
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T11:52:18.174021+00:00
-- url     : https://prove2.me/submissions/9b158359-603b-4921-a0a9-9317d1e32d15

import Mathlib
import Definitions.Def_FedergruenTzur_MinPred_Omega
import Definitions.Def_FedergruenTzur_MinPred_RankedList



namespace FedergruenTzur.MinPred

open LotSizing

lemma ftz_sumsplit (P : LotSizing) (s : Finset ℕ) (X : ℝ) :
    ∑ r ∈ s, P.h r * (X - P.D r) = X * ∑ r ∈ s, P.h r - ∑ r ∈ s, P.h r * P.D r := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun _ _ => by ring

lemma ftz_Hdiff (P : LotSizing) (k n : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n + 1) :
    P.H n - P.H (k - 1) = ∑ r ∈ Finset.Ico k (n + 1), P.h r := by
  unfold LotSizing.H
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [← Finset.Ico_add_one_right_eq_Icc, ← Finset.Ico_add_one_right_eq_Icc, ← Finset.sum_Ico_consecutive _ (show 1 ≤ k' + 1 by omega) hkn]
  ring

lemma ftz_diff (P : LotSizing) (j k l : ℕ) (hk : 1 ≤ k) (hkl : k < l) (hlj : l ≤ j) (x : ℝ) :
    P.potCost j k x - P.potCost j l x = P.A k l + (P.Ctil k - P.Ctil l) * x := by
  obtain ⟨n, rfl⟩ : ∃ n, l = n + 1 := ⟨l - 1, by omega⟩
  have hH := ftz_Hdiff P k n hk (by omega)
  have hS : P.S k j = P.S (n+1) j + ∑ r ∈ Finset.Ico k (n + 1), P.h r * (P.D j - P.D r) := by
    unfold LotSizing.S
    rw [← Finset.sum_Ico_consecutive _ (show k ≤ n + 1 by omega) hlj]; ring
  have hc : P.cij k (n+1) = P.c k + ∑ r ∈ Finset.Ico k (n + 1), P.h r := rfl
  unfold LotSizing.potCost LotSizing.A LotSizing.Ctil
  rw [hS, hc]
  simp only [Nat.add_sub_cancel]
  unfold LotSizing.S
  simp only [Finset.sum_Ico_succ_top (show k ≤ n by omega)] at hH ⊢
  simp only [ftz_sumsplit]
  have hk1 : P.H (k - 1) = P.H n - (∑ r ∈ Finset.Ico k n, P.h r + P.h n) := by linarith
  rw [hk1]
  ring


def ftzR (P : LotSizing) (p q : ℕ) : Prop :=
  P.Ctil q < P.Ctil p ∨ (P.Ctil p = P.Ctil q ∧ p < q)

lemma ftz_pair (P : LotSizing) (j p q : ℕ) (hp : 1 ≤ p ∧ p ≤ j) (hq : 1 ≤ q ∧ q ≤ j)
    (hR : ftzR P p q) (x : ℝ) :
    (P.G q p < (x : EReal) → P.potCost j q x < P.potCost j p x) ∧
    ((x : EReal) < P.G q p → (P.potCost j p x < P.potCost j q x ∨
        (P.potCost j p x = P.potCost j q x ∧ p < q))) ∧
    ((x : EReal) < P.G q p → P.G q p ≠ ⊤ → P.potCost j p x < P.potCost j q x) := by
  rcases lt_trichotomy p q with hpq | rfl | hpq
  · have hG : P.G q p = P.Gord p q := by unfold LotSizing.G; rw [if_neg (by omega)]
    have d := ftz_diff P j p q hp.1 hpq hq.2 x
    rw [hG]; unfold LotSizing.Gord
    by_cases hc : P.Ctil q ≠ P.Ctil p
    · have hlt : P.Ctil q < P.Ctil p := by
        rcases hR with h | h
        · exact h
        · exact absurd h.1.symm hc
      rw [if_pos hc]
      simp only [EReal.coe_lt_coe_iff]
      have hs : P.Ctil q - P.Ctil p < 0 := by linarith
      refine ⟨fun h => ?_, fun h => ?_, fun h _ => ?_⟩
      · rw [div_lt_iff_of_neg hs] at h; nlinarith
      · rw [lt_div_iff_of_neg hs] at h; left; nlinarith
      · rw [lt_div_iff_of_neg hs] at h; nlinarith
    · push Not at hc
      rw [if_neg (by simpa using hc)]
      rw [hc] at d
      split_ifs with hA
      · refine ⟨fun h => absurd h not_top_lt, fun _ => ?_, fun _ hne => absurd rfl hne⟩
        rcases hA.lt_or_eq with hA | hA
        · left; linarith
        · right; exact ⟨by linarith, hpq⟩
      · refine ⟨fun _ => by push Not at hA; linarith, fun h => absurd h (not_lt_bot), fun h => absurd h (not_lt_bot)⟩
  · exfalso; rcases hR with h | h
    · exact lt_irrefl _ h
    · exact lt_irrefl _ h.2
  · have hG : P.G q p = P.Gord q p := by unfold LotSizing.G; rw [if_pos (by omega)]
    have d := ftz_diff P j q p hq.1 hpq hp.2 x
    have hlt : P.Ctil q < P.Ctil p := by
      rcases hR with h | h
      · exact h
      · omega
    have hc : P.Ctil p ≠ P.Ctil q := ne_of_gt hlt
    rw [hG]; unfold LotSizing.Gord
    rw [if_pos hc]
    simp only [EReal.coe_lt_coe_iff]
    have hs : 0 < P.Ctil p - P.Ctil q := by linarith
    refine ⟨fun h => ?_, fun h => ?_, fun h _ => ?_⟩
    · rw [div_lt_iff₀ hs] at h; nlinarith
    · rw [lt_div_iff₀ hs] at h; left; nlinarith
    · rw [lt_div_iff₀ hs] at h; nlinarith

lemma ftz_pair_top (P : LotSizing) (j p q : ℕ) (hp : 1 ≤ p ∧ p ≤ j) (hq : 1 ≤ q ∧ q ≤ j)
    (hR : ftzR P p q) (hG : P.G q p = ⊤) : p < q ∧ ∀ y, P.potCost j p y ≤ P.potCost j q y := by
  rcases lt_trichotomy p q with hpq | rfl | hpq
  · have hG' : P.G q p = P.Gord p q := by unfold LotSizing.G; rw [if_neg (by omega)]
    rw [hG'] at hG; unfold LotSizing.Gord at hG
    refine ⟨hpq, fun y => ?_⟩
    have d := ftz_diff P j p q hp.1 hpq hq.2 y
    split_ifs at hG with h1 h2
    · exact absurd hG (EReal.coe_ne_top _)
    · push Not at h1; rw [h1] at d; linarith
    · exact absurd hG (by simp)
  · exfalso; rcases hR with h | h
    · exact lt_irrefl _ h
    · exact lt_irrefl _ h.2
  · exfalso
    have hG' : P.G q p = P.Gord q p := by unfold LotSizing.G; rw [if_pos (by omega)]
    have hlt : P.Ctil q < P.Ctil p := by
      rcases hR with h | h
      · exact h
      · omega
    rw [hG'] at hG; unfold LotSizing.Gord at hG
    rw [if_pos (ne_of_gt hlt)] at hG
    exact EReal.coe_ne_top _ hG


lemma ftz_mem (P : LotSizing) (j : ℕ) (L : List ℕ) (hL : P.IsRanked j L) (m : ℕ)
    (hm : m < L.length) : L.getD m 0 ∈ L ∧ 1 ≤ L.getD m 0 ∧ L.getD m 0 ≤ j := by
  have h1 : L.getD m 0 ∈ L := by
    rw [List.getD_eq_getElem _ _ hm]; exact List.getElem_mem hm
  exact ⟨h1, hL.2.1 _ h1⟩

lemma ftz_R (P : LotSizing) (j : ℕ) (L : List ℕ) (hL : P.IsRanked j L) (i k : ℕ)
    (hik : i < k) (hk : k < L.length) : ftzR P (L.getD i 0) (L.getD k 0) := by
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hk]
  exact (List.pairwise_iff_getElem.mp hL.2.2) i k (by omega) hk hik

lemma ftz_gval_succ (P : LotSizing) (j : ℕ) (L : List ℕ) (t : ℕ) :
    P.gval j L (t + 1) = P.G (L.getD (t + 1) 0) (L.getD t 0) := by
  unfold LotSizing.gval; simp

lemma ftz_cons (P : LotSizing) (j : ℕ) (L : List ℕ) (hL : P.IsRanked j L) (t : ℕ)
    (ht : t + 1 < L.length) (x : ℝ) :
    (P.gval j L (t + 1) < (x : EReal) →
        P.potCost j (L.getD (t + 1) 0) x < P.potCost j (L.getD t 0) x) ∧
    ((x : EReal) < P.gval j L (t + 1) →
      (P.potCost j (L.getD t 0) x < P.potCost j (L.getD (t + 1) 0) x ∨
        (P.potCost j (L.getD t 0) x = P.potCost j (L.getD (t + 1) 0) x ∧
          L.getD t 0 < L.getD (t + 1) 0))) ∧
    ((x : EReal) < P.gval j L (t + 1) → P.gval j L (t + 1) ≠ ⊤ →
        P.potCost j (L.getD t 0) x < P.potCost j (L.getD (t + 1) 0) x) := by
  rw [ftz_gval_succ]
  have a := ftz_mem P j L hL t (by omega)
  have b := ftz_mem P j L hL (t + 1) ht
  exact ftz_pair P j _ _ a.2 b.2 (ftz_R P j L hL t (t + 1) (by omega) ht) x

lemma ftz_mono (P : LotSizing) (j : ℕ) (L : List ℕ) (h6 : P.Cond6 j L) :
    ∀ a b, a < b → b < L.length → P.gval j L a < P.gval j L b := by
  intro a b hab hb
  induction b with
  | zero => omega
  | succ b ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hab with h | h
    · exact (ih h (by omega)).trans (h6.1 b hb)
    · subst h; exact h6.1 a hb

lemma ftz_mono_le (P : LotSizing) (j : ℕ) (L : List ℕ) (h6 : P.Cond6 j L) :
    ∀ a b, a ≤ b → b < L.length → P.gval j L a ≤ P.gval j L b := by
  intro a b hab hb
  rcases hab.lt_or_eq with h | h
  · exact (ftz_mono P j L h6 a b h hb).le
  · rw [h]

lemma ftz_ne_top (P : LotSizing) (j : ℕ) (L : List ℕ) (h6 : P.Cond6 j L) (b : ℕ)
    (hb : b < L.length) : P.gval j L b < ⊤ :=
  lt_of_le_of_lt (ftz_mono_le P j L h6 b (L.length - 1) (by omega) (by omega)) h6.2

theorem chain_core (P : LotSizing) (j : ℕ) (L : List ℕ) (hL : P.IsRanked j L)
    (h6 : P.Cond6 j L) (m : ℕ) (hm : m < L.length) (x : ℝ)
    (hlow : m = 0 ∨ P.gval j L m < (x : EReal))
    (hup : L.length ≤ m + 1 ∨ (x : EReal) < P.gval j L (m + 1)) :
    ∀ l ∈ L, l ≠ L.getD m 0 → P.potCost j (L.getD m 0) x < P.potCost j l x := by
  intro l hl hne
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hl
  rw [← List.getD_eq_getElem _ 0 hi] at hne ⊢
  rcases lt_trichotomy i m with him | rfl | him
  · have hgm : P.gval j L m < (x : EReal) := by
      rcases hlow with h | h
      · omega
      · exact h
    have key : ∀ n t, t + n + 1 = m →
        P.potCost j (L.getD m 0) x < P.potCost j (L.getD t 0) x := by
      intro n
      induction n with
      | zero =>
        intro t ht
        subst ht
        exact (ftz_cons P j L hL t (by omega) x).1 hgm
      | succ n ih =>
        intro t ht
        have h1 := ih (t + 1) (by omega)
        have hg : P.gval j L (t + 1) < (x : EReal) :=
          lt_of_le_of_lt (ftz_mono_le P j L h6 (t + 1) m (by omega) hm) hgm
        exact h1.trans ((ftz_cons P j L hL t (by omega) x).1 hg)
    exact key (m - i - 1) i (by omega)
  · exact absurd rfl hne
  · have hgm : (x : EReal) < P.gval j L (m + 1) := by
      rcases hup with h | h
      · omega
      · exact h
    have key : ∀ n, m + n + 1 < L.length →
        P.potCost j (L.getD m 0) x < P.potCost j (L.getD (m + n + 1) 0) x := by
      intro n
      induction n with
      | zero =>
        intro ht
        exact (ftz_cons P j L hL m ht x).2.2 hgm (ftz_ne_top P j L h6 _ ht).ne
      | succ n ih =>
        intro ht
        have h1 := ih (by omega)
        have hg : (x : EReal) < P.gval j L (m + n + 1 + 1) :=
          lt_of_lt_of_le hgm (ftz_mono_le P j L h6 (m + 1) _ (by omega) ht)
        exact h1.trans ((ftz_cons P j L hL (m + n + 1) ht x).2.2 hg (ftz_ne_top P j L h6 _ ht).ne)
    have := key (i - m - 1) (by omega)
    rwa [show m + (i - m - 1) + 1 = i by omega] at this


lemma ftz_omega_iff (P : LotSizing) (j l : ℕ) : l ∈ P.Omega j ↔ (1 ≤ l ∧ l ≤ j) ∧
    ∃ a b : ℝ, P.D j ≤ a ∧ a < b ∧ ∀ x ∈ Set.Ioo a b, P.IsLowestOptimal j l x := by
  unfold LotSizing.Omega
  simp [Finset.mem_filter, Finset.mem_Icc]

theorem c3_core (P : LotSizing) (j : ℕ) (L : List ℕ)
    (hL : P.IsRanked j L) (hΩ : P.Omega j ⊆ L.toFinset) (hlen : 0 < L.length)
    (hg : P.gval j L (L.length - 1) = ⊤) :
    P.Omega j ⊆ L.toFinset.erase (L.getD (L.length - 1) 0) := by
  intro l hl
  refine Finset.mem_erase.mpr ⟨?_, hΩ hl⟩
  rintro rfl
  obtain ⟨t, ht⟩ : ∃ t, L.length - 1 = t + 1 := by
    rcases Nat.eq_zero_or_pos (L.length - 1) with h | h
    · rw [h] at hg; unfold LotSizing.gval at hg; simp at hg
    · exact ⟨L.length - 1 - 1, by omega⟩
  rw [ht] at hg hl
  rw [ftz_gval_succ] at hg
  have a := ftz_mem P j L hL t (by omega)
  have b := ftz_mem P j L hL (t + 1) (by omega)
  obtain ⟨hpq, hle⟩ := ftz_pair_top P j _ _ a.2 b.2 (ftz_R P j L hL t (t + 1) (by omega) (by omega)) hg
  obtain ⟨_, a', b', _, hab, hopt⟩ := (ftz_omega_iff P j _).mp hl
  have hx := (hopt ((a' + b') / 2) ⟨by linarith, by linarith⟩).2 (L.getD t 0)
    (Finset.mem_Icc.mpr a.2) hpq
  linarith [hle ((a' + b') / 2)]

theorem c1_core (P : LotSizing) (j : ℕ) (L : List ℕ)
    (hL : P.IsRanked j L) (hΩ : P.Omega j ⊆ L.toFinset) (hlen : 1 < L.length)
    (hg : P.gval j L 1 ≤ ((P.D j : ℝ) : EReal)) :
    P.Omega j ⊆ L.toFinset.erase (L.getD 0 0) := by
  intro l hl
  refine Finset.mem_erase.mpr ⟨?_, hΩ hl⟩
  rintro rfl
  obtain ⟨_, a', b', hDa, hab, hopt⟩ := (ftz_omega_iff P j _).mp hl
  have b := ftz_mem P j L hL 1 hlen
  have hx := (hopt ((a' + b') / 2) ⟨by linarith, by linarith⟩).1 (L.getD 1 0)
    (Finset.mem_Icc.mpr b.2)
  have hlt : P.gval j L (0 + 1) < (((a' + b') / 2 : ℝ) : EReal) :=
    lt_of_le_of_lt hg (EReal.coe_lt_coe_iff.mpr (by linarith))
  have := (ftz_cons P j L hL 0 hlen _).1 hlt
  linarith

theorem c2_core (P : LotSizing) (j : ℕ) (L : List ℕ)
    (hL : P.IsRanked j L) (hΩ : P.Omega j ⊆ L.toFinset) (m : ℕ) (hm : 1 ≤ m)
    (hmr : m + 1 < L.length) (hg : P.gval j L (m + 1) ≤ P.gval j L m) :
    P.Omega j ⊆ L.toFinset.erase (L.getD m 0) := by
  intro l hl
  refine Finset.mem_erase.mpr ⟨?_, hΩ hl⟩
  rintro rfl
  obtain ⟨_, a', b', hDa, hab, hopt⟩ := (ftz_omega_iff P j _).mp hl
  obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
  have pm := ftz_mem P j L hL t (by omega)
  have sm := ftz_mem P j L hL (t + 2) hmr
  have hup : ∀ x ∈ Set.Ioo a' b', (x : EReal) ≤ P.gval j L (t + 1 + 1) := by
    intro x hx
    by_contra hc
    push Not at hc
    have h1 := (ftz_cons P j L hL (t + 1) hmr x).1 hc
    have h2 := (hopt x hx).1 (L.getD (t + 2) 0) (Finset.mem_Icc.mpr sm.2)
    linarith
  have hlo : ∀ x ∈ Set.Ioo a' b', P.gval j L (t + 1) ≤ (x : EReal) := by
    intro x hx
    by_contra hc
    push Not at hc
    have h1 := (ftz_cons P j L hL t (by omega) x).2.1 hc
    have h2 := (hopt x hx).1 (L.getD t 0) (Finset.mem_Icc.mpr pm.2)
    have h3 := (hopt x hx).2 (L.getD t 0) (Finset.mem_Icc.mpr pm.2)
    rcases h1 with h1 | ⟨h1, h1'⟩
    · linarith
    · linarith [h3 h1']
  have e1 := hlo ((2 * a' + b') / 3) ⟨by linarith, by linarith⟩
  have e2 := hup ((a' + 2 * b') / 3) ⟨by linarith, by linarith⟩
  have : (((a' + 2 * b') / 3 : ℝ) : EReal) ≤ (((2 * a' + b') / 3 : ℝ) : EReal) :=
    e2.trans (hg.trans e1)
  rw [EReal.coe_le_coe_iff] at this
  linarith

end FedergruenTzur.MinPred

open FedergruenTzur.MinPred


theorem solution (P : LotSizing) (j : ℕ) (hj : 1 ≤ j) (L : List ℕ)
    (hL : P.IsRanked j L) (hΩ : P.Omega j ⊆ L.toFinset) (hlen : 0 < L.length)
    (hg : P.gval j L (L.length - 1) = ⊤) :
    P.Omega j ⊆ L.toFinset.erase (L.getD (L.length - 1) 0) := by
  exact c3_core P j L hL hΩ hlen hg
