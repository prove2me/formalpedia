-- Prove2me | solution 1 for GDGen3.small_step_square_bound
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:48:00.63104+00:00
-- url     : https://prove2.me/submissions/392d8de4-26ef-4b29-8fe3-1e75f154fd0b

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase

noncomputable section

open Finset

open GDGen3

namespace GDGen3Proof_small_step_square_bound

theorem prefix_telescope (ξ : ℕ → ℝ) (h0 : ξ 0 = 0) (hne : ∀ i : ℕ, i ≠ 0 → ξ i ≠ 0) :
    ∀ i : ℕ, Finset.sum (range i) (fun j => Abar ξ j) = ξ i * Abar ξ i := by
  intro i
  induction i with
  | zero => simp [Abar, h0]
  | succ k ih =>
    have h1 : ξ (k + 1) ≠ 0 := hne (k + 1) (by omega)
    rw [sum_range_succ, ih]
    simp only [Abar]
    field_simp
    ring

lemma Abar_ne_zero (ξ : ℕ → ℝ) (h0 : ξ 0 = 0) (hpos : ∀ i : ℕ, i ≠ 0 → 0 < ξ i) :
    ∀ i : ℕ, Abar ξ i ≠ 0 := by
  intro i
  induction i with
  | zero => simp [Abar]
  | succ k ih =>
    have h1 : 1 + ξ k ≠ 0 := by
      by_cases hk : k = 0
      · simp [hk, h0]
      · have := hpos k hk; linarith
    rw [Abar]
    exact div_ne_zero (mul_ne_zero ih h1) (ne_of_gt (hpos (k + 1) (by omega)))

lemma quad_eta (r : ℝ) (N : ℕ) (ξ : ℕ → ℝ)
    (hquad : ∀ i : ℕ, i < N → pj r (i + 1) * ξ i * (1 + ξ i + C r N i) = X r N i) (i : ℕ) (hi : i < N) :
    pj r (i + 1) * ξ i * (1 + eta r N ξ i) = X r N i := by
  simpa only [eta, add_assoc] using hquad i hi

lemma eta_last_zero (r : ℝ) (N : ℕ) (hN : 1 ≤ N) (ξ : ℕ → ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hpos : ∀ i : ℕ, i ≠ 0 → 0 < ξ i) (h0 : ξ 0 = 0)
    (hquad : ∀ i : ℕ, i < N → pj r (i + 1) * ξ i * (1 + ξ i + C r N i) = X r N i)
    (hpin : pj r N * ξ (N - 1) = X r N (N - 1)) :
    eta r N ξ (N - 1) = 0 := by
  by_cases hN1 : N = 1
  · subst N
    have hpne : pj r 1 ≠ 0 := by
      unfold pj
      have hlt : r ^ (2 * 1) < 1 := pow_lt_one₀ (le_of_lt hr) hr1 (by omega)
      exact div_ne_zero (by linarith) (by positivity)
    simp only [eta, Nat.sub_self, h0, zero_add, C, M, PiS, sum_range_succ,
      sum_range_zero, zero_add, Nat.cast_one]
    field_simp [hpne]
    ring
  have h := quad_eta r N ξ hquad (N - 1) (by omega)
  rw [← hpin] at h
  have hlt : r ^ (2 * N) < 1 := by
    have h2 : 2 * N ≠ 0 := by omega
    have hN0 : N ≠ 0 := by omega
    exact pow_lt_one₀ (le_of_lt hr) hr1 (by omega)
  have hpj : pj r N ≠ 0 := by
    simp only [pj]
    exact div_ne_zero (by linarith) (by positivity)
  have hne : pj r N * ξ (N - 1) ≠ 0 := mul_ne_zero hpj (ne_of_gt (hpos (N - 1) (by omega)))
  have h' : pj r N * ξ (N - 1) * (1 + eta r N ξ (N - 1)) = pj r N * ξ (N - 1) := by
    simpa [Nat.sub_add_cancel hN] using h
  have h1 : 1 + eta r N ξ (N - 1) = 1 := by
    apply mul_left_cancel₀ hne
    rw [mul_one]
    exact h'
  linarith

lemma eta_recur_holds (r : ℝ) (N : ℕ) (hN : 1 ≤ N) (ξ : ℕ → ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hpos : ∀ i : ℕ, i ≠ 0 → 0 < ξ i) (h0 : ξ 0 = 0)
    (hquad : ∀ i : ℕ, i < N → pj r (i + 1) * ξ i * (1 + eta r N ξ i) = X r N i)
    (hquad7 : ∀ i : ℕ, i < N → pj r (i + 1) * eta r N ξ i * (1 + ξ i) = X r N (i + 1)) :
    eta_recur_prop r N ξ := by
  intro i hi hiN
  have h6 : pj r (i + 1) * ξ i * (1 + eta r N ξ i) = X r N i := hquad i (by omega)
  have h7 : pj r i * eta r N ξ (i - 1) * (1 + ξ (i - 1)) = X r N i := by
    have h := hquad7 (i - 1) (by omega)
    have hidx : i - 1 + 1 = i := by omega
    simpa only [hidx] using h
  have hA : Abar ξ i = Abar ξ (i - 1) * (1 + ξ (i - 1)) / ξ i := by
    have hi1 : i = (i - 1) + 1 := by omega
    conv_lhs => rw [hi1]
    rw [Abar]
    have : i - 1 + 1 = i := by omega
    rw [this]
  have hAne : Abar ξ (i - 1) ≠ 0 := Abar_ne_zero ξ h0 hpos (i - 1)
  have hxne : ξ i ≠ 0 := ne_of_gt (hpos i (by omega))
  have h1ne : 1 + ξ (i - 1) ≠ 0 := by
    by_cases hi0 : i - 1 = 0
    · simp [hi0, h0]
    · have := hpos (i - 1) hi0; linarith
  have hD : D r ξ N i = pj r i / Abar ξ (i - 1) := by
    rw [D, if_neg (by omega : ¬ (i = 0 ∨ N < i)), Am,
        if_neg (by omega : ¬ i = 0)]
  have hD1 : D r ξ N (i + 1) = pj r (i + 1) / Abar ξ i := by
    have h0 : ¬ (i + 1 = 0 ∨ N < i + 1) := by omega
    have h2 : i + 1 - 1 = i := by omega
    rw [D, if_neg h0, Am, if_neg (by omega : ¬ i + 1 = 0), h2]
  have key : eta r N ξ (i - 1) * (pj r i) * (1 + ξ (i - 1))
      = pj r (i + 1) * (1 + eta r N ξ i) * ξ i := by
    linear_combination h7 - h6
  rw [hD, hD1, hA]
  field_simp
  linear_combination key

theorem suffix_telescope (r : ℝ) (N : ℕ) (hN : 1 ≤ N) (ξ : ℕ → ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hpos : ∀ i : ℕ, i ≠ 0 → 0 < ξ i) (h0 : ξ 0 = 0)
    (hquad : ∀ i : ℕ, i < N → pj r (i + 1) * ξ i * (1 + ξ i + C r N i) = X r N i)
    (hrec : eta_recur_prop r N ξ)
    (hpin : pj r N * ξ (N - 1) = X r N (N - 1)) :
    ∀ i : ℕ, i + 1 ≤ N →
      Finset.sum (Icc (i + 2) N) (fun j => D r ξ N j) = eta r N ξ i * D r ξ N (i + 1) := by
  have hlast : eta r N ξ (N - 1) = 0 :=
    eta_last_zero r N hN ξ hr hr1 hpos h0 hquad hpin
  have key : ∀ k : ℕ, ∀ i : ℕ, N - 1 - i = k → i + 1 ≤ N →
      Finset.sum (Icc (i + 2) N) (fun j => D r ξ N j) = eta r N ξ i * D r ξ N (i + 1) := by
    intro k
    induction k with
    | zero =>
      intro i hk hi
      have hiN : i = N - 1 := by omega
      subst hiN
      rw [Finset.sum_eq_zero (by intro x hx; simp only [Finset.mem_Icc] at hx; omega), hlast]
      ring
    | succ k ih =>
      intro i hk hi
      have hi2 : i + 2 ≤ N := by omega
      have hk' : N - 1 - (i + 1) = k := by omega
      have hi' : i + 1 + 1 ≤ N := by omega
      have ihk := ih (i + 1) hk' hi'
      have hsplit : Icc (i + 2) N = insert (i + 2) (Icc (i + 3) N) := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hsplit, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), ihk]
      have hrec' : eta r N ξ i * D r ξ N (i + 1) = D r ξ N (i + 2) * (1 + eta r N ξ (i + 1)) := by
        have h := hrec (i + 1) (by omega) hi'
        simpa only [Nat.add_sub_cancel] using h
      rw [hrec']
      ring
  intro i hi
  exact key (N - 1 - i) i rfl hi


/-! ## Section 5 layer: the flow `d`, the certificate sum, and (20) -/

lemma sum_antisymm (F : ℕ → ℕ → ℝ) (s : Finset ℕ) :
    Finset.sum s (fun k => Finset.sum s (fun j => (F k j - F j k))) = 0 := by
  simp only [Finset.sum_sub_distrib]
  rw [Finset.sum_comm (s := s) (t := s)
        (f := fun a b => F b a)]
  simp

lemma ell_of_lt (r : ℝ) (ξ : ℕ → ℝ) (N : ℕ) {k j : ℕ} (h : k < j) :
    ell r ξ N k j = (Abar ξ k - Am ξ k) * (D r ξ N j + r * D r ξ N (j + 1)) := by
  simp only [ell, if_pos h]

lemma ell_of_gt (r : ℝ) (ξ : ℕ → ℝ) (N : ℕ) {k j : ℕ} (h : j < k) :
    ell r ξ N k j = (Am ξ j + r * Abar ξ j) * (D r ξ N k - D r ξ N (k + 1)) := by
  rw [ell, if_neg (Nat.not_lt.mpr (le_of_lt h))]

lemma am_telescope (ξ : ℕ → ℝ) : ∀ i : ℕ,
    Finset.sum (Finset.range (i + 1)) (fun k => Abar ξ k - Am ξ k) = Abar ξ i := by
  intro i
  induction i with
  | zero => simp [Am, Abar]
  | succ m ih =>
    have hstep : Am ξ (m + 1) = Abar ξ m := by
      rw [Am, if_neg (by omega : ¬ m + 1 = 0), Nat.add_sub_cancel]
    rw [Finset.sum_range_succ, ih, hstep]
    ring

lemma am_sum (ξ : ℕ → ℝ) (h0 : ξ 0 = 0) : ∀ i : ℕ,
    Finset.sum (Finset.range (i + 1)) (fun k => Am ξ k)
      = Finset.sum (Finset.range i) (fun k => Abar ξ k) := by
  intro i
  induction i with
  | zero => simp [Am]
  | succ m ih =>
    have hstep : Am ξ (m + 1) = Abar ξ m := by
      rw [Am, if_neg (by omega : ¬ m + 1 = 0), Nat.add_sub_cancel]
    rw [Finset.sum_range_succ, ih, hstep, Finset.sum_range_succ]

lemma am_telescope2 (ξ : ℕ → ℝ) (h0 : ξ 0 = 0) (r : ℝ) (i : ℕ) :
    Finset.sum (Finset.range (i + 1)) (fun k => Am ξ k + r * Abar ξ k)
      = (Finset.sum (Finset.range i) (fun k => Abar ξ k))
        + r * (Abar ξ i + Finset.sum (Finset.range i) (fun k => Abar ξ k)) := by
  have hsplit : Finset.sum (Finset.range (i + 1)) (fun k => Am ξ k + r * Abar ξ k)
      = Finset.sum (Finset.range (i + 1)) (fun k => Am ξ k)
        + r * Finset.sum (Finset.range (i + 1)) (fun k => Abar ξ k) := by
    rw [Finset.mul_sum, Finset.sum_add_distrib]
  rw [hsplit, am_sum ξ h0 i, Finset.sum_range_succ]
  ring

lemma D_telescope (r : ℝ) (ξ : ℕ → ℝ) (N i : ℕ) (hi : i + 1 ≤ N) :
    Finset.sum (Finset.Icc (i + 1) N) (fun j => D r ξ N j - D r ξ N (j + 1)) = D r ξ N (i + 1) := by
  have hDN : D r ξ N (N + 1) = 0 := by
    rw [D, if_pos (Or.inr (by omega : N < N + 1))]
  have key : ∀ M, i + 1 ≤ M → M ≤ N →
      Finset.sum (Finset.Icc (i + 1) M) (fun j => D r ξ N j - D r ξ N (j + 1))
        = D r ξ N (i + 1) - D r ξ N (M + 1) := by
    intro M h1 _
    induction M, h1 using Nat.le_induction with
    | base => simp
    | succ b hb ih =>
      rw [Finset.sum_Icc_succ_top (a := i + 1) (b := b) (by omega), ih (by omega)]
      ring
  rw [key N hi le_rfl, hDN, sub_zero]

lemma flow_prefix_split (r : ℝ) (ξ : ℕ → ℝ) (N i : ℕ) (hi : i ≤ N) :
    Finset.sum (Finset.range (i + 1)) (fun k => d r ξ N k)
      = Finset.sum (Finset.range (i + 1))
          (fun k => Finset.sum (Finset.Icc (i + 1) N) (fun j => ell r ξ N k j - ell r ξ N j k)) := by
  have hsplit : ∀ k, d r ξ N k
      = Finset.sum (Finset.range (i + 1)) (fun j => ell r ξ N k j - ell r ξ N j k)
        + Finset.sum (Finset.Icc (i + 1) N) (fun j => ell r ξ N k j - ell r ξ N j k) := by
    intro k
    have hN : Finset.range (i + 1) ∪ Finset.Icc (i + 1) N = Finset.range (N + 1) := by
      ext x
      simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Icc]
      omega
    have hdisj : Disjoint (Finset.range (i + 1)) (Finset.Icc (i + 1) N) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [Finset.mem_range] at hx
      simp only [Finset.mem_Icc] at hx'
      omega
    show Finset.sum (Finset.range (N + 1)) _ = _
    rw [← hN, Finset.sum_union hdisj]
  simp only [hsplit, Finset.sum_add_distrib]
  rw [sum_antisymm (fun k j => ell r ξ N k j) (Finset.range (i + 1)), zero_add]

lemma cross_inner (r : ℝ) (ξ : ℕ → ℝ) (N i j : ℕ)
    (h0 : ξ 0 = 0) (hne : ∀ i : ℕ, i ≠ 0 → ξ i ≠ 0)
    (hij : i < j) (hjN : j ≤ N) :
    Finset.sum (Finset.range (i + 1)) (fun k => ell r ξ N k j - ell r ξ N j k)
      = (D r ξ N j + r * D r ξ N (j + 1)) * Abar ξ i
        - (D r ξ N j - D r ξ N (j + 1))
          * ((Finset.sum (Finset.range i) (fun k => Abar ξ k))
              + r * Abar ξ i
              + r * (Finset.sum (Finset.range i) (fun k => Abar ξ k))) := by
  have hterm : ∀ k ∈ Finset.range (i + 1),
      ell r ξ N k j - ell r ξ N j k
        = (Abar ξ k - Am ξ k) * (D r ξ N j + r * D r ξ N (j + 1))
          - (Am ξ k + r * Abar ξ k) * (D r ξ N j - D r ξ N (j + 1)) := by
    intro k hk
    simp only [Finset.mem_range] at hk
    have hkj : k < j := by omega
    have hjk : ¬ (j < k) := by omega
    simp only [ell, if_pos hkj, if_neg hjk]
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
    am_telescope ξ i, am_telescope2 ξ h0 r i]
  ring

lemma cross_outer (r : ℝ) (ξ : ℕ → ℝ) (N i : ℕ) (hi : i + 1 ≤ N)
    (h0 : ξ 0 = 0) (hne : ∀ i : ℕ, i ≠ 0 → ξ i ≠ 0) :
    Finset.sum (Finset.Icc (i + 1) N)
        (fun j => (D r ξ N j + r * D r ξ N (j + 1)) * Abar ξ i
          - (D r ξ N j - D r ξ N (j + 1))
            * ((Finset.sum (Finset.range i) (fun k => Abar ξ k)) + r * Abar ξ i
                + r * (Finset.sum (Finset.range i) (fun k => Abar ξ k))))
      = (1 - r) * (Abar ξ i * D r ξ N (i + 1))
        + (1 + r) * (Abar ξ i * (Finset.sum (Finset.Icc (i + 2) N) (fun j => D r ξ N j))
            - D r ξ N (i + 1) * (Finset.sum (Finset.range i) (fun k => Abar ξ k))) := by
  have hP : Finset.sum (Finset.range i) (fun k => Abar ξ k) = ξ i * Abar ξ i :=
    prefix_telescope ξ h0 hne i
  have htel := D_telescope r ξ N i hi
  have hsplit : Finset.sum (Finset.Icc (i + 1) N)
        (fun j => (D r ξ N j + r * D r ξ N (j + 1)) * Abar ξ i
          - (D r ξ N j - D r ξ N (j + 1))
            * ((Finset.sum (Finset.range i) (fun k => Abar ξ k)) + r * Abar ξ i
                + r * (Finset.sum (Finset.range i) (fun k => Abar ξ k))))
      = Abar ξ i * Finset.sum (Finset.Icc (i + 1) N) (fun j => D r ξ N j + r * D r ξ N (j + 1))
        - ((Finset.sum (Finset.range i) (fun k => Abar ξ k)) + r * Abar ξ i
            + r * (Finset.sum (Finset.range i) (fun k => Abar ξ k)))
          * Finset.sum (Finset.Icc (i + 1) N) (fun j => D r ξ N j - D r ξ N (j + 1)) := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
    ring
  rw [hsplit, htel]
  have hre : Finset.sum (Finset.Icc (i + 1) N) (fun j => D r ξ N j + r * D r ξ N (j + 1))
      = D r ξ N (i + 1) + (1 + r) * Finset.sum (Finset.Icc (i + 2) N) (fun j => D r ξ N j) := by
    have hDN : D r ξ N (N + 1) = 0 := by
      rw [D, if_pos (Or.inr (by omega : N < N + 1))]
    rw [Finset.sum_add_distrib]
    have h2 : Finset.sum (Finset.Icc (i + 1) N) (fun j => r * D r ξ N (j + 1))
        = r * Finset.sum (Finset.Icc (i + 2) (N + 1)) (fun j => D r ξ N j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_bij (fun j _ => j + 1)
      · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
      · intro a _ b _ h; omega
      · intro b hb
        simp only [Finset.mem_Icc] at hb
        exact ⟨b - 1, by simp only [Finset.mem_Icc]; omega, by omega⟩
      · intro a _; rfl
    have hpeel : ∀ M, i + 1 ≤ M → M ≤ N →
        Finset.sum (Finset.Icc (i + 1) M) (fun j => D r ξ N j)
          = D r ξ N (i + 1) + Finset.sum (Finset.Icc (i + 2) M) (fun j => D r ξ N j) := by
      intro M h1 _
      induction M, h1 using Nat.le_induction with
      | base =>
        rw [Finset.Icc_self, Finset.sum_singleton]
        have : Finset.Icc (i + 2) (i + 1) = (∅ : Finset ℕ) := by
          apply Finset.Icc_eq_empty_of_lt
          omega
        rw [this, Finset.sum_empty, add_zero]
      | succ b hb ih =>
        rw [Finset.sum_Icc_succ_top (a := i + 1) (b := b) (by omega),
          ih (by omega), Finset.sum_Icc_succ_top (a := i + 2) (b := b) (by omega)]
        ring
    rw [h2, hpeel N (by omega) le_rfl,
      Finset.sum_Icc_succ_top (a := i + 2) (b := N) (by omega), hDN, add_zero]
    ring
  rw [hre]
  rw [hP]
  ring

theorem flow_identity (r : ℝ) (N : ℕ) (hN : 1 ≤ N) (ξ : ℕ → ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hpos : ∀ i : ℕ, i ≠ 0 → 0 < ξ i) (h0 : ξ 0 = 0)
    (hquad : ∀ i : ℕ, i < N → pj r (i + 1) * ξ i * (1 + eta r N ξ i) = X r N i)
    (hquad7 : ∀ i : ℕ, i < N → pj r (i + 1) * eta r N ξ i * (1 + ξ i) = X r N (i + 1))
    (hpin : pj r N * ξ (N - 1) = X r N (N - 1)) (i : ℕ) (hi : i + 1 ≤ N) :
    Finset.sum (Finset.range (i + 1)) (fun k => d r ξ N k) = M r N * (i + 1) := by
  have hne : ∀ i : ℕ, i ≠ 0 → ξ i ≠ 0 := fun i hi => ne_of_gt (hpos i hi)
  have hrec := eta_recur_holds r N hN ξ hr hr1 hpos h0 hquad hquad7
  have hAiD : Abar ξ i * D r ξ N (i + 1) = pj r (i + 1) := by
    have h1 : ¬ (i + 1 = 0 ∨ N < i + 1) := by omega
    rw [D, if_neg h1, Am, if_neg (by omega : ¬ i + 1 = 0)]
    have h2 : i + 1 - 1 = i := by omega
    have hAne : Abar ξ i ≠ 0 := Abar_ne_zero ξ h0 hpos i
    rw [h2]
    field_simp
  have hsum : Finset.sum (Finset.Icc (i + 2) N) (fun j => D r ξ N j)
      = eta r N ξ i * D r ξ N (i + 1) :=
    suffix_telescope r N hN ξ hr hr1 hpos h0
      (fun k hk => by simpa only [eta, add_assoc] using hquad k hk) hrec hpin i hi
  have hPref : Finset.sum (Finset.range i) (fun k => Abar ξ k) = ξ i * Abar ξ i :=
    prefix_telescope ξ h0 hne i
  rw [flow_prefix_split r ξ N i (le_of_lt hi)]
  rw [Finset.sum_comm]
  have hinner : ∀ j ∈ Finset.Icc (i + 1) N,
      Finset.sum (Finset.range (i + 1)) (fun k => ell r ξ N k j - ell r ξ N j k)
        = (D r ξ N j + r * D r ξ N (j + 1)) * Abar ξ i
          - (D r ξ N j - D r ξ N (j + 1))
            * ((Finset.sum (Finset.range i) (fun k => Abar ξ k)) + r * Abar ξ i
                + r * (Finset.sum (Finset.range i) (fun k => Abar ξ k))) := by
    intro j hj
    simp only [Finset.mem_Icc] at hj
    exact cross_inner r ξ N i j h0 hne (by omega) hj.2
  rw [Finset.sum_congr rfl hinner, cross_outer r ξ N i hi h0 hne, hPref, hsum, hAiD]
  have hpne : pj r (i + 1) ≠ 0 := by
    have hlt : r ^ (2 * (i + 1)) < 1 := by
      have hN0 : 2 * (i + 1) ≠ 0 := by omega
      exact pow_lt_one₀ (le_of_lt hr) hr1 hN0
    rw [pj]
    exact div_ne_zero (by linarith) (by positivity)
  rw [eta, C]
  field_simp [hpne]
  rw [hAiD]
  ring

/-! ## Section 5 assembly: the certificate sum and (20) for arbitrary N -/

theorem rV_sub_U (r : ℝ) (N i : ℕ) (hN : 1 ≤ N) (ξ : ℕ → ℝ) (h0 : ξ 0 = 0)
    (hpos : ∀ i : ℕ, i ≠ 0 → 0 < ξ i) (hr : r ≠ 0) (hi : i + 1 ≤ N) :
    r * V r ξ N i - U r ξ N i = (1 - r ^ 2) / 2 := by
  have hV : V r ξ N i = (Am ξ i + r * Abar ξ i) * D r ξ N (i + 1) := by
    unfold V
    have ht : ∀ j ∈ Icc (i + 1) N, ell r ξ N j i =
        (Am ξ i + r * Abar ξ i) * (D r ξ N j - D r ξ N (j + 1)) := by
      intro j hj
      exact ell_of_gt r ξ N (by simp only [mem_Icc] at hj; omega)
    rw [sum_congr rfl ht, ← mul_sum, D_telescope r ξ N i hi]
  have hU : U r ξ N i = (D r ξ N i + r * D r ξ N (i + 1)) * Am ξ i := by
    unfold U
    have ht : ∀ j ∈ range i, ell r ξ N j i =
        (Abar ξ j - Am ξ j) * (D r ξ N i + r * D r ξ N (i + 1)) := by
      intro j hj
      exact ell_of_lt r ξ N (mem_range.mp hj)
    rw [sum_congr rfl ht, ← sum_mul]
    cases i with
    | zero => simp [Am]
    | succ k => rw [am_telescope ξ k]; simp [Am, mul_comm]
  have hAD : Abar ξ i * D r ξ N (i + 1) = pj r (i + 1) := by
    simp only [D, if_neg (by omega : ¬(i + 1 = 0 ∨ N < i + 1)),
      Am, if_neg (by omega : i + 1 ≠ 0), Nat.add_sub_cancel]
    exact mul_div_cancel₀ _ (Abar_ne_zero ξ h0 hpos i)
  have hamD : Am ξ i * D r ξ N i = pj r i := by
    by_cases hi0 : i = 0
    · subst i; simp [Am, D, pj]
    · simp only [D, if_neg (by omega : ¬(i = 0 ∨ N < i))]
      have ha : Am ξ i ≠ 0 := by
        simpa [Am, hi0] using Abar_ne_zero ξ h0 hpos (i - 1)
      exact mul_div_cancel₀ _ ha
  have hp : r ^ 2 * pj r (i + 1) - pj r i = (1 - r ^ 2) / 2 := by
    simp only [pj, Nat.mul_add, pow_add]
    field_simp
    ring
  calc
    r * V r ξ N i - U r ξ N i =
        r ^ 2 * (Abar ξ i * D r ξ N (i + 1)) - Am ξ i * D r ξ N i := by
      rw [hV, hU]; ring
    _ = r ^ 2 * pj r (i + 1) - pj r i := by rw [hAD, hamD]
    _ = (1 - r ^ 2) / 2 := hp

lemma sum_prefix_indicator (F : ℕ → ℝ) (B a : ℕ) (ha : a ≤ B) :
    (∑ k ∈ range B, if k < a then F k else 0) = ∑ k ∈ range a, F k := by
  rw [← sum_filter]
  congr 1
  ext k
  simp only [mem_filter, mem_range]
  omega

lemma sum_suffix_indicator (F : ℕ → ℝ) (N a : ℕ) :
    (∑ k ∈ range (N + 1), if a < k then F k else 0) = ∑ k ∈ Icc (a + 1) N, F k := by
  rw [← sum_filter]
  congr 1
  ext k
  simp only [mem_filter, mem_range, mem_Icc]
  omega

lemma symmetric_sum_diagonal (B P : ℕ → ℕ → ℝ) (N : ℕ)
    (hP : ∀ i j, P i j = P j i)
    (hB : ∀ i j, i ≤ N → j ≤ N → i ≠ j → B i j + B j i = 0) :
    (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), B i j * P i j)
      = ∑ i ∈ range (N + 1), B i i * P i i := by
  let T := fun i j => if i = j then (0 : ℝ) else B i j * P i j
  have ht : ∀ i ∈ range (N + 1), ∀ j ∈ range (N + 1), T i j = -T j i := by
    intro i hi j hj
    by_cases hij : i = j
    · subst j; simp [T]
    · simp only [T, if_neg hij, if_neg (Ne.symm hij)]
      rw [hP j i]
      have hb := hB i j (by simpa using hi) (by simpa using hj) hij
      linear_combination P i j * hb
  have hz : (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), T i j) = 0 := by
    have he : (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), T i j) =
        -(∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), T i j) := by
      calc
        _ = ∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), -T j i := by
          apply sum_congr rfl; intro i hi
          apply sum_congr rfl; intro j hj
          exact ht i hi j hj
        _ = _ := by simp only [sum_neg_distrib]; rw [sum_comm]
    linarith
  have he : ∀ i ∈ range (N + 1), ∀ j ∈ range (N + 1),
      B i j * P i j = T i j + if i = j then B i i * P i i else 0 := by
    intro i hi j hj
    by_cases h : i = j <;> simp [T, h]
  rw [sum_congr rfl (fun i hi => sum_congr rfl (he i hi))]
  simp only [sum_add_distrib]
  rw [hz, zero_add]
  apply sum_congr rfl
  intro i hi
  simp [sum_ite_eq, hi]

lemma weighted_ginner (h : ℝ) (N : ℕ) (L P : ℕ → ℕ → ℝ) :
    (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), L i j * ginner h P i j) =
      h * ∑ j ∈ range (N + 1), ∑ k ∈ range (N + 1),
        ((if k < j then ∑ i ∈ range (N + 1), L i j else 0)
          - ∑ i ∈ range (N + 1), if k < i then L i j else 0) * P j k := by
  have hg : ∀ i ∈ range (N + 1), ∀ j ∈ range (N + 1),
      L i j * ginner h P i j = h * ∑ k ∈ range (N + 1),
        ((if k < j then L i j else 0) - (if k < i then L i j else 0)) * P j k := by
    intro i hi j hj
    unfold ginner
    rw [← sum_prefix_indicator (fun k => P j k) (N + 1) j (by exact le_of_lt (mem_range.mp hj)),
      ← sum_prefix_indicator (fun k => P j k) (N + 1) i (by exact le_of_lt (mem_range.mp hi))]
    rw [← mul_assoc]
    simp only [mul_sub, mul_sum, sum_sub_distrib, sub_mul]
    rw [← sum_sub_distrib, ← sum_sub_distrib]
    apply sum_congr rfl
    intro k hk
    split_ifs <;> ring
  rw [sum_congr rfl (fun i hi => sum_congr rfl (hg i hi))]
  simp only [← mul_sum]
  congr 1
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  rw [sum_comm]
  apply sum_congr rfl
  intro k hk
  rw [← sum_mul, sum_sub_distrib]
  congr 1
  by_cases hk : k < j <;> simp [hk]

lemma ell_pair_sum (r : ℝ) (ξ : ℕ → ℝ) (N a b : ℕ) (hab : a < b) :
    ell r ξ N a b + ell r ξ N b a =
      (1 + r) * (Abar ξ a * D r ξ N b - Am ξ a * D r ξ N (b + 1)) := by
  rw [ell_of_lt r ξ N hab, ell_of_gt r ξ N hab]
  ring

lemma incoming_prefix (r : ℝ) (ξ : ℕ → ℝ) (N a b : ℕ) (hab : a < b) :
    (∑ i ∈ range (a + 1), ell r ξ N i b) =
      Abar ξ a * (D r ξ N b + r * D r ξ N (b + 1)) := by
  have ht : ∀ i ∈ range (a + 1), ell r ξ N i b =
      (Abar ξ i - Am ξ i) * (D r ξ N b + r * D r ξ N (b + 1)) := by
    intro i hi
    exact ell_of_lt r ξ N (by simp only [mem_range] at hi; omega)
  rw [sum_congr rfl ht, ← sum_mul, am_telescope]

lemma incoming_suffix (r : ℝ) (ξ : ℕ → ℝ) (N a b : ℕ)
    (hab : a ≤ b) (hb : b ≤ N) :
    (∑ i ∈ Icc (b + 1) N, ell r ξ N i a) =
      (Am ξ a + r * Abar ξ a) * D r ξ N (b + 1) := by
  by_cases hbN : b = N
  · subst b
    simp [Icc_eq_empty_of_lt (by omega : N < N + 1), D]
  · have ht : ∀ i ∈ Icc (b + 1) N, ell r ξ N i a =
        (Am ξ a + r * Abar ξ a) * (D r ξ N i - D r ξ N (i + 1)) := by
      intro i hi
      exact ell_of_gt r ξ N (by simp only [mem_Icc] at hi; omega)
    rw [sum_congr rfl ht, ← mul_sum, D_telescope r ξ N b (by omega)]

lemma mixed_coeff_cancel (r : ℝ) (ξ : ℕ → ℝ) (N a b : ℕ)
    (hab : a < b) (hb : b ≤ N) :
    ell r ξ N a b + ell r ξ N b a =
      (1 + r) * ((∑ i ∈ range (a + 1), ell r ξ N i b)
        - ∑ i ∈ Icc (b + 1) N, ell r ξ N i a) := by
  rw [ell_pair_sum r ξ N a b hab, incoming_prefix r ξ N a b hab,
    incoming_suffix r ξ N a b (le_of_lt hab) hb]
  ring

lemma total_sub_suffix (F : ℕ → ℝ) (N a : ℕ) (ha : a ≤ N) :
    (∑ i ∈ range (N + 1), F i) - (∑ i ∈ range (N + 1), if a < i then F i else 0)
      = ∑ i ∈ range (a + 1), F i := by
  rw [← sum_sub_distrib, ← sum_prefix_indicator F (N + 1) (a + 1) (by omega)]
  apply sum_congr rfl
  intro i hi
  by_cases h : a < i
  · simp [h, show ¬i < a + 1 by omega]
  · simp [h, show i < a + 1 by omega]

lemma weighted_function_values (L : ℕ → ℕ → ℝ) (f : ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), L i j * (f i - f j)) =
      ∑ i ∈ range (N + 1), (∑ j ∈ range (N + 1), (L i j - L j i)) * f i := by
  simp only [sum_sub_distrib, sum_mul, sub_mul, mul_sub]
  congr 1
  rw [sum_comm]

lemma weighted_squares (L P : ℕ → ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), L i j * (P i i + P j j)) =
      ∑ i ∈ range (N + 1), (∑ j ∈ range (N + 1), (L i j + L j i)) * P i i := by
  simp only [sum_add_distrib, sum_mul, add_mul, mul_add]
  congr 1
  rw [sum_comm]

lemma internal_coefficients (r : ℝ) (ξ : ℕ → ℝ) (N : ℕ)
    (f : ℕ → ℝ) (P : ℕ → ℕ → ℝ) (hP : ∀ i j, P i j = P j i) :
    2 * (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1),
      if i = j then 0 else ell r ξ N i j * Qv (1 + r) f P i j) =
    ∑ i ∈ range (N + 1), (2 * d r ξ N i * f i
      + (2 * (1 + r) * V r ξ N i - (∑ j ∈ range (N + 1),
          (ell r ξ N i j + ell r ξ N j i)) + 2 * ell r ξ N i i) * P i i) := by
  let L := ell r ξ N
  let B := fun j k => L j k - (1 + r) *
    ((if k < j then ∑ i ∈ range (N + 1), L i j else 0)
      - ∑ i ∈ range (N + 1), if k < i then L i j else 0)
  have hb : ∀ i j, i ≤ N → j ≤ N → i ≠ j → B i j + B j i = 0 := by
    suffices hs : ∀ i j, i < j → j ≤ N → B i j + B j i = 0 by
      intro i j hi hj hij
      rcases lt_or_gt_of_ne hij with h | h
      · exact hs i j h hj
      · rw [add_comm]; exact hs j i h hi
    intro i j hij hj
    have hi : i ≤ N := by omega
    simp only [B, if_pos hij, if_neg (by omega : ¬j < i), zero_sub, mul_neg, sub_neg_eq_add]
    rw [total_sub_suffix (fun a => L a j) N i hi,
      sum_suffix_indicator (fun a => L a i) N j]
    have hc := mixed_coeff_cancel r ξ N i j hij hj
    dsimp [L] at *
    linear_combination hc
  have hdiag : ∀ i, B i i = L i i + (1 + r) * V r ξ N i := by
    intro i
    simp only [B, lt_self_iff_false, if_false, zero_sub, mul_neg, sub_neg_eq_add]
    rw [sum_suffix_indicator]
    rfl
  have hz := symmetric_sum_diagonal B P N hP hb
  simp_rw [hdiag] at hz
  have hg := weighted_ginner (1 + r) N L P
  have hmix : (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1),
      L i j * P i j) - (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1),
      L i j * ginner (1 + r) P i j) =
      ∑ i ∈ range (N + 1), (L i i + (1 + r) * V r ξ N i) * P i i := by
    rw [hg, ← hz]
    simp only [B, sub_mul, mul_assoc, sum_sub_distrib, ← mul_sum]
  have hq : ∀ i j, (if i = j then 0 else L i j * Qv (1 + r) f P i j)
      = L i j * Qv (1 + r) f P i j := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp only [Qv, ginner, sub_self, mul_zero]
      ring_nf
      simp
    · simp [hij]
  have he : (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), L i j * Qv (1 + r) f P i j) =
      (∑ i ∈ range (N + 1), (∑ j ∈ range (N + 1), (L i j - L j i)) * f i)
      - (1 / 2) * (∑ i ∈ range (N + 1), (∑ j ∈ range (N + 1), (L i j + L j i)) * P i i)
      + (∑ i ∈ range (N + 1), (L i i + (1 + r) * V r ξ N i) * P i i) := by
    have ht : ∀ i j, L i j * Qv (1 + r) f P i j =
        L i j * (f i - f j) - (1 / 2) * (L i j * (P i i + P j j))
        + L i j * P i j - L i j * ginner (1 + r) P i j := by
      intro i j; unfold Qv; ring
    simp only [ht, sum_sub_distrib, sum_add_distrib, ← mul_sum]
    rw [weighted_function_values, weighted_squares]
    simp only [sum_sub_distrib, sum_add_distrib]
    linear_combination hmix
  change 2 * (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1),
    if i = j then 0 else L i j * Qv (1 + r) f P i j) = _
  simp_rw [hq]
  rw [he]
  simp only [d]
  rw [mul_sum, ← sum_sub_distrib, ← sum_add_distrib, mul_sum]
  apply sum_congr rfl
  intro i hi
  dsimp [L]
  ring

lemma incoming_sum (r : ℝ) (ξ : ℕ → ℝ) (N i : ℕ) (hi : i ≤ N) :
    (∑ j ∈ range (N + 1), ell r ξ N j i) = U r ξ N i + ell r ξ N i i + V r ξ N i := by
  have h := total_sub_suffix (fun j => ell r ξ N j i) N i hi
  have hp : (∑ j ∈ range (i + 1), ell r ξ N j i) =
      (∑ j ∈ range i, ell r ξ N j i) + ell r ξ N i i := sum_range_succ _ i
  rw [hp, sum_suffix_indicator] at h
  unfold U V
  linarith

lemma diagonal_coeff (r : ℝ) (ξ : ℕ → ℝ) (N i : ℕ) (hi : i ≤ N) :
    2 * (1 + r) * V r ξ N i - (∑ j ∈ range (N + 1), (ell r ξ N i j + ell r ξ N j i))
      + 2 * ell r ξ N i i = 2 * (r * V r ξ N i - U r ξ N i) - d r ξ N i := by
  have h := incoming_sum r ξ N i hi
  simp only [d, sum_sub_distrib, sum_add_distrib]
  linear_combination -2 * h

lemma flow_at_index (r : ℝ) (N : ℕ) (hN : 1 ≤ N) (ξ : ℕ → ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hpos : ∀ i : ℕ, i ≠ 0 → 0 < ξ i) (h0 : ξ 0 = 0)
    (hquad : ∀ i : ℕ, i < N → pj r (i + 1) * ξ i * (1 + eta r N ξ i) = X r N i)
    (hquad7 : ∀ i : ℕ, i < N → pj r (i + 1) * eta r N ξ i * (1 + ξ i) = X r N (i + 1))
    (hpin : pj r N * ξ (N - 1) = X r N (N - 1)) (i : ℕ) (hi : i < N) :
    d r ξ N i = M r N := by
  have h := flow_identity r N hN ξ hr hr1 hpos h0 hquad hquad7 hpin i (by omega)
  by_cases hi0 : i = 0
  · subst i; simpa using h
  · have hprev := flow_identity r N hN ξ hr hr1 hpos h0 hquad hquad7 hpin (i - 1) (by omega)
    have hid : i - 1 + 1 = i := by omega
    rw [hid] at hprev
    have hcast : ((i - 1 : ℕ) : ℝ) + 1 = (i : ℝ) := by exact_mod_cast hid
    rw [hcast] at hprev
    rw [sum_range_succ] at h
    norm_num only [Nat.cast_add, Nat.cast_one] at h
    linarith

lemma flow_total (r : ℝ) (ξ : ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ range (N + 1), d r ξ N i) = 0 := by
  exact sum_antisymm (ell r ξ N) (range (N + 1))

lemma U_last (r : ℝ) (N : ℕ) (hN : 1 ≤ N) (ξ : ℕ → ℝ) (h0 : ξ 0 = 0)
    (hpos : ∀ i : ℕ, i ≠ 0 → 0 < ξ i) : U r ξ N N = pj r N := by
  have ht : ∀ j ∈ range N, ell r ξ N j N =
      (Abar ξ j - Am ξ j) * (D r ξ N N + r * D r ξ N (N + 1)) := by
    intro j hj; exact ell_of_lt r ξ N (mem_range.mp hj)
  unfold U
  rw [sum_congr rfl ht, ← sum_mul]
  have hid : N - 1 + 1 = N := by omega
  have ha := am_telescope ξ (N - 1)
  rw [hid] at ha
  rw [ha]
  have hDN1 : D r ξ N (N + 1) = 0 := by simp [D]
  rw [hDN1, mul_zero, add_zero]
  simp only [D, if_neg (by omega : ¬(N = 0 ∨ N < N)),
    Am, if_neg (by omega : N ≠ 0)]
  exact mul_div_cancel₀ _ (Abar_ne_zero ξ h0 hpos (N - 1))

lemma V_last (r : ℝ) (ξ : ℕ → ℝ) (N : ℕ) : V r ξ N N = 0 := by
  simp [V]

lemma pj_zpow (r : ℝ) (hr : r ≠ 0) (N : ℕ) :
    2 * pj r N = r ^ (-(2 * (N : ℤ))) - 1 := by
  rw [zpow_neg]
  have he : (2 * (N : ℤ)) = ((2 * N : ℕ) : ℤ) := by simp
  rw [he, zpow_natCast]
  unfold pj
  field_simp

theorem internal_reduction
    (r : ℝ) (N : ℕ) (hN : 1 ≤ N) (ξ : ℕ → ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hpos : ∀ i : ℕ, i ≠ 0 → 0 < ξ i) (h0 : ξ 0 = 0)
    (hquad : ∀ i : ℕ, i < N → pj r (i + 1) * ξ i * (1 + eta r N ξ i) = X r N i)
    (hquad7 : ∀ i : ℕ, i < N → pj r (i + 1) * eta r N ξ i * (1 + ξ i) = X r N (i + 1))
    (hpin : pj r N * ξ (N - 1) = X r N (N - 1))
    (f : ℕ → ℝ) (P : ℕ → ℕ → ℝ) (hP : ∀ i j, P i j = P j i) :
    2 * Finset.sum (Finset.range (N + 1)) (fun i =>
        Finset.sum (Finset.range (N + 1)) (fun j =>
          if i = j then 0 else ell r ξ N i j * Qv (1 + r) f P i j))
      = 2 * M r N * Finset.sum (Finset.range N) (fun i => f i - f N)
        + (1 - r ^ 2 - M r N) * Finset.sum (Finset.range N) (fun i => P i i)
        + ((N : ℝ) * M r N - r ^ (-(2 * (N : ℤ))) + 1) * P N N := by
  have hdi : ∀ i, i < N → d r ξ N i = M r N :=
    fun i hi => flow_at_index r N hN ξ hr hr1 hpos h0 hquad hquad7 hpin i hi
  have hsumd : (∑ i ∈ range N, d r ξ N i) = (N : ℝ) * M r N := by
    rw [sum_congr rfl (fun i hi => hdi i (mem_range.mp hi))]
    simp [mul_comm]
  have hdN : d r ξ N N = -(N : ℝ) * M r N := by
    have h := flow_total r ξ N
    rw [sum_range_succ, hsumd] at h
    linarith
  have hterm : ∀ i ∈ range N,
      2 * d r ξ N i * f i + (2 * (1 + r) * V r ξ N i
        - (∑ j ∈ range (N + 1), (ell r ξ N i j + ell r ξ N j i))
        + 2 * ell r ξ N i i) * P i i =
      2 * M r N * f i + (1 - r ^ 2 - M r N) * P i i := by
    intro i hi
    have hiN : i < N := mem_range.mp hi
    rw [diagonal_coeff r ξ N i (by omega), hdi i hiN,
      rV_sub_U r N i hN ξ h0 hpos (ne_of_gt hr) (by omega)]
    ring
  have hlast : 2 * d r ξ N N * f N + (2 * (1 + r) * V r ξ N N
        - (∑ j ∈ range (N + 1), (ell r ξ N N j + ell r ξ N j N))
        + 2 * ell r ξ N N N) * P N N =
      -2 * (N : ℝ) * M r N * f N +
        ((N : ℝ) * M r N - r ^ (-(2 * (N : ℤ))) + 1) * P N N := by
    rw [diagonal_coeff r ξ N N le_rfl, hdN, V_last, U_last r N hN ξ h0 hpos]
    have hp := pj_zpow r (ne_of_gt hr) N
    linear_combination -P N N * hp
  rw [internal_coefficients r ξ N f P hP, sum_range_succ, hlast,
    sum_congr rfl hterm]
  simp only [sum_add_distrib, ← mul_sum, sum_sub_distrib, sum_const,
    card_range, nsmul_eq_mul]
  ring

lemma symmetric_square_telescope (P : ℕ → ℕ → ℝ) (hP : ∀ i j, P i j = P j i) (N : ℕ) :
    2 * (∑ i ∈ range N, ∑ j ∈ range i, P i j) + (∑ i ∈ range N, P i i) =
      ∑ i ∈ range N, ∑ j ∈ range N, P i j := by
  induction N with
  | zero => simp
  | succ n ih =>
    simp only [sum_range_succ, sum_add_distrib]
    have he : (∑ i ∈ range n, P i n) = ∑ i ∈ range n, P n i := by
      apply sum_congr rfl; intro i hi; exact hP i n
    rw [he]
    linear_combination ih

lemma pj_pos (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (j : ℕ) (hj : j ≠ 0) :
    0 < pj r j := by
  have ht : r ^ (2 * j) < 1 := pow_lt_one₀ (le_of_lt hr) hr1 (by omega)
  exact div_pos (by linarith) (by positivity)

lemma pj_geometric (r : ℝ) (hr : r ≠ 0) (j : ℕ) :
    pj r j = ((1 / r ^ 2) ^ j - 1) / 2 := by
  unfold pj
  simp only [div_pow, one_pow, ← pow_mul]
  field_simp

lemma pow_slope_strictMono (z : ℝ) (hz : 1 < z) :
    StrictMono (fun n : ℕ => (z ^ (n + 1) - 1) / ((n : ℝ) + 1)) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hsum : (∑ k ∈ range (n + 1), z ^ k) < ((n : ℝ) + 1) * z ^ (n + 1) := by
    calc
      _ < ∑ k ∈ range (n + 1), z ^ (n + 1) := by
        apply sum_lt_sum
        · intro k hk; exact le_of_lt (pow_lt_pow_right₀ hz (mem_range.mp hk))
        · exact ⟨0, by simp, pow_lt_pow_right₀ hz (by omega)⟩
      _ = _ := by simp
  have hm := mul_lt_mul_of_pos_right hsum (by linarith : 0 < z - 1)
  rw [geom_sum_mul] at hm
  apply (div_lt_div_iff₀ (by positivity : 0 < (n : ℝ) + 1)
    (by positivity : 0 < ((n + 1 : ℕ) : ℝ) + 1)).2
  simp only [Nat.cast_add, Nat.cast_one, pow_succ]
  rw [pow_succ] at hm
  nlinarith

lemma pj_slope_strictMono (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    StrictMono (fun n : ℕ => pj r (n + 1) / ((n : ℝ) + 1)) := by
  have hz : 1 < 1 / r ^ 2 := by
    apply (lt_div_iff₀ (by positivity : 0 < r ^ 2)).2
    have ht : r ^ 2 < 1 := pow_lt_one₀ (le_of_lt hr) hr1 (by omega)
    simpa using ht
  intro a b hab
  have h := pow_slope_strictMono (1 / r ^ 2) hz hab
  dsimp at h ⊢
  rw [pj_geometric r (ne_of_gt hr), pj_geometric r (ne_of_gt hr)]
  have he : ∀ k : ℕ, (((1 / r ^ 2) ^ (k + 1) - 1) / 2) / ((k : ℝ) + 1) =
      (((1 / r ^ 2) ^ (k + 1) - 1) / ((k : ℝ) + 1)) / 2 := by intro k; ring
  rw [he, he]
  exact div_lt_div_of_pos_right h (by norm_num)

lemma nat_prefix_weight (n : ℕ) :
    2 * (∑ k ∈ range n, ((k : ℝ) + 1)) = (n : ℝ) * ((n : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    norm_num only [Nat.cast_add, Nat.cast_one]
    nlinarith

lemma PiS_next_strict (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (n : ℕ) (hn : 0 < n) :
    2 * PiS r n < (n : ℝ) * pj r (n + 1) := by
  have ht : ∀ k ∈ range n,
      pj r (k + 1) * ((n : ℝ) + 1) < pj r (n + 1) * ((k : ℝ) + 1) := by
    intro k hk
    have h := pj_slope_strictMono r hr hr1 (mem_range.mp hk)
    exact (div_lt_div_iff₀ (by positivity) (by positivity)).mp h
  have hsum : (∑ k ∈ range n, pj r (k + 1) * ((n : ℝ) + 1)) <
      ∑ k ∈ range n, pj r (n + 1) * ((k : ℝ) + 1) := by
    apply sum_lt_sum
    · intro k hk; exact le_of_lt (ht k hk)
    · exact ⟨0, mem_range.mpr hn, ht 0 (mem_range.mpr hn)⟩
  rw [← sum_mul, ← mul_sum] at hsum
  have hw := nat_prefix_weight n
  change PiS r n * ((n : ℝ) + 1) < pj r (n + 1) * _ at hsum
  have hnpos : 0 < (n : ℝ) + 1 := by positivity
  have hmul : (2 * PiS r n - (n : ℝ) * pj r (n + 1)) * ((n : ℝ) + 1) < 0 := by
    nlinarith [mul_nonneg (le_of_lt (pj_pos r hr hr1 (n + 1) (by omega))) (le_of_lt hnpos)]
  have hd : 2 * PiS r n - (n : ℝ) * pj r (n + 1) < 0 := by
    by_contra hneg
    have hnon := mul_nonneg (le_of_not_gt hneg) (le_of_lt hnpos)
    linarith
  exact sub_neg.mp hd

lemma PiS_average_strictMono (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    StrictMono (fun n : ℕ => PiS r (n + 1) / (((n : ℝ) + 1) * ((n : ℝ) + 2))) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have ht := PiS_next_strict r hr hr1 (n + 1) (by omega)
  simp only [Nat.cast_add, Nat.cast_one] at ht ⊢
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
  simp only [PiS, sum_range_succ] at *
  nlinarith

lemma pj_step (r : ℝ) (hr : r ≠ 0) (i : ℕ) :
    r ^ 2 * pj r (i + 1) - pj r i = (1 - r ^ 2) / 2 := by
  simp only [pj, Nat.mul_add, pow_add]
  field_simp
  ring

lemma PiS_closed (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (i : ℕ) :
    PiS r i = pj r i / (1 - r ^ 2) - (i : ℝ) / 2 := by
  have hr2 : r ^ 2 < 1 := pow_lt_one₀ (le_of_lt hr) hr1 (by omega)
  have hne : 1 - r ^ 2 ≠ 0 := by linarith
  induction i with
  | zero => simp [PiS, pj]
  | succ i ih =>
    have hp := pj_step r (ne_of_gt hr) i
    change PiS r (i + 1) = _
    rw [PiS, sum_range_succ]
    change PiS r i + pj r (i + 1) = _
    rw [ih]
    push_cast
    field_simp [hne]
    nlinarith [hp]

lemma X_zero (r : ℝ) (N : ℕ) : X r N 0 = 0 := by simp [X, PiS]

lemma X_last (r : ℝ) (hr : 0 < r) (N : ℕ) (hN : 1 ≤ N) : X r N N = 0 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  unfold X M
  field_simp
  ring

lemma X_pos (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ) (hi : 1 ≤ i) (hiN : i < N) :
    0 < X r N i := by
  have hNi : 1 ≤ N := by omega
  have hci : ((i - 1 : ℕ) : ℝ) + 1 = (i : ℝ) := by exact_mod_cast Nat.sub_add_cancel hi
  have hcN : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by exact_mod_cast Nat.sub_add_cancel hNi
  have hm := PiS_average_strictMono r hr hr1 (by omega : i - 1 < N - 1)
  dsimp at hm
  rw [Nat.sub_add_cancel hi, Nat.sub_add_cancel hNi] at hm
  have hci2 : ((i - 1 : ℕ) : ℝ) + 2 = (i : ℝ) + 1 := by linarith
  have hcN2 : ((N - 1 : ℕ) : ℝ) + 2 = (N : ℝ) + 1 := by linarith
  rw [hci, hcN, hci2, hcN2] at hm
  have hipos : 0 < (i : ℝ) := by exact_mod_cast (show 0 < i by omega)
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hc := (div_lt_div_iff₀ (by positivity) (by positivity)).mp hm
  unfold X M
  apply div_pos
  · have hden : 0 < (N : ℝ) * ((N : ℝ) + 1) := by positivity
    have hnum : 0 < (1 - r) *
        ((i : ℝ) * ((i : ℝ) + 1) * PiS r N - (N : ℝ) * ((N : ℝ) + 1) * PiS r i) :=
      mul_pos (by linarith) (by nlinarith [hc])
    have he : 2 * (1 - r) * PiS r N / ((N : ℝ) * ((N : ℝ) + 1)) * (i : ℝ) * ((i : ℝ) + 1) / 2
        - (1 - r) * PiS r i =
        ((1 - r) * ((i : ℝ) * ((i : ℝ) + 1) * PiS r N - (N : ℝ) * ((N : ℝ) + 1) * PiS r i)) /
          ((N : ℝ) * ((N : ℝ) + 1)) := by field_simp
    rw [he]
    exact div_pos hnum hden
  · positivity

lemma X_step (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ) :
    X r N (i + 1) - X r N i = pj r (i + 1) * C r N i := by
  have hp : pj r (i + 1) ≠ 0 := ne_of_gt (pj_pos r hr hr1 (i + 1) (by omega))
  unfold X C
  rw [PiS, sum_range_succ]
  change (M r N * ((i + 1 : ℕ) : ℝ) * (((i + 1 : ℕ) : ℝ) + 1) / 2
      - (1 - r) * (PiS r i + pj r (i + 1))) / (1 + r)
    - (M r N * (i : ℝ) * ((i : ℝ) + 1) / 2 - (1 - r) * PiS r i) / (1 + r) = _
  push_cast
  field_simp [hp]
  ring

lemma rootXi_zero (r : ℝ) (N : ℕ) : rootXi r N 0 = 0 := by simp [rootXi]

lemma rootXi_pos (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ) (hi : i ≠ 0) :
    0 < rootXi r N i := by
  unfold rootXi
  rw [if_neg hi]
  by_cases hiN : i < N
  · rw [if_pos hiN]
    have hx := X_pos r hr hr1 N i (by omega) hiN
    have hp := pj_pos r hr hr1 (i + 1) (by omega)
    have hdisc : (1 + C r N i) ^ 2 < (1 + C r N i) ^ 2 + 4 * X r N i / pj r (i + 1) := by
      have hd : 0 < 4 * X r N i / pj r (i + 1) := div_pos (by positivity) hp
      linarith
    have hsq : |1 + C r N i| < Real.sqrt ((1 + C r N i) ^ 2 + 4 * X r N i / pj r (i + 1)) := by
      rw [← Real.sqrt_sq_eq_abs (1 + C r N i)]
      exact Real.sqrt_lt_sqrt (sq_nonneg _) hdisc
    have hb := le_abs_self (1 + C r N i)
    linarith
  · simp [hiN]

lemma rootXi_quad (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ) (hiN : i < N) :
    pj r (i + 1) * rootXi r N i * (1 + eta r N (rootXi r N) i) = X r N i := by
  by_cases hi : i = 0
  · subst i; simp [rootXi_zero, X_zero]
  · have hx := X_pos r hr hr1 N i (by omega) hiN
    have hp := pj_pos r hr hr1 (i + 1) (by omega)
    have hd : 0 ≤ (1 + C r N i) ^ 2 + 4 * X r N i / pj r (i + 1) := by positivity
    have hs := Real.sq_sqrt hd
    unfold eta
    simp only [rootXi, if_neg hi, if_pos hiN]
    have hm : pj r (i + 1) * (4 * X r N i / pj r (i + 1)) = 4 * X r N i :=
      mul_div_cancel₀ _ (ne_of_gt hp)
    nlinarith [hs, hm]

lemma rootXi_quad7 (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ) (hiN : i < N) :
    pj r (i + 1) * eta r N (rootXi r N) i * (1 + rootXi r N i) = X r N (i + 1) := by
  have hq := rootXi_quad r hr hr1 N i hiN
  have hx := X_step r hr hr1 N i
  unfold eta at *
  linear_combination hq - hx

lemma rootXi_nonneg (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ) : 0 ≤ rootXi r N i := by
  by_cases hi : i = 0
  · subst i; rw [rootXi_zero]
  · exact le_of_lt (rootXi_pos r hr hr1 N i hi)

lemma rootXi_eta_last (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N : ℕ) (hN : 1 ≤ N) :
    eta r N (rootXi r N) (N - 1) = 0 := by
  have h := rootXi_quad7 r hr hr1 N (N - 1) (by omega)
  rw [Nat.sub_add_cancel hN, X_last r hr N hN] at h
  have hp : pj r N ≠ 0 := ne_of_gt (pj_pos r hr hr1 N (by omega))
  have hx : 1 + rootXi r N (N - 1) ≠ 0 := by
    have hn := rootXi_nonneg r hr hr1 N (N - 1)
    linarith
  simpa only [mul_eq_zero, hp, hx, false_or, or_false] using h

lemma rootXi_pin (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N : ℕ) (hN : 1 ≤ N) :
    pj r N * rootXi r N (N - 1) = X r N (N - 1) := by
  have h := rootXi_quad r hr hr1 N (N - 1) (by omega)
  simpa only [Nat.sub_add_cancel hN, rootXi_eta_last r hr hr1 N hN, add_zero, mul_one] using h

lemma M_gap (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N : ℕ) (hN : 1 ≤ N) :
    (1 + r) - M r N =
      ((1 + (N : ℝ) * (1 + r)) ^ 2 - 1 / r ^ (2 * N)) /
        ((1 + r) * (N : ℝ) * ((N : ℝ) + 1)) := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hr2 : 1 - r ^ 2 ≠ 0 := by
    have ht : r ^ 2 < 1 := pow_lt_one₀ (le_of_lt hr) hr1 (by omega)
    linarith
  unfold M
  rw [PiS_closed r hr hr1 N]
  unfold pj
  field_simp
  ring

lemma M_le_h (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N : ℕ) (hN : 1 ≤ N)
    (hbranch : 1 / r ^ N ≤ 1 + (N : ℝ) * (1 + r)) : M r N ≤ 1 + r := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hb : (1 / r ^ N) ^ 2 ≤ (1 + (N : ℝ) * (1 + r)) ^ 2 := by
    have hi : 0 ≤ 1 / r ^ N := by positivity
    nlinarith
  have he : (1 / r ^ N) ^ 2 = 1 / r ^ (2 * N) := by
    rw [Nat.mul_comm 2 N, pow_mul, div_pow, one_pow]
  rw [he] at hb
  have hgap : 0 ≤ (1 + r) - M r N := by
    rw [M_gap r hr hr1 N hN]
    apply div_nonneg (by linarith) (by positivity)
  linarith

lemma referenceXi_zero (r : ℝ) (hr : 0 < r) : referenceXi r 0 = 0 := by simp [referenceXi]

lemma reference_power_bound (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ)
    (hi : 1 ≤ i) (hiN : i < N)
    (hbranch : 1 / r ^ N ≤ 1 + (N : ℝ) * (1 + r)) :
    1 / r ^ i < 1 + (i : ℝ) * (1 + r) := by
  have hz : 1 < 1 / r := (lt_div_iff₀ hr).2 (by simpa using hr1)
  have hs := pow_slope_strictMono (1 / r) hz (by omega : i - 1 < N - 1)
  dsimp at hs
  have hN : 1 ≤ N := by omega
  rw [Nat.sub_add_cancel hi, Nat.sub_add_cancel hN] at hs
  have hci : ((i - 1 : ℕ) : ℝ) + 1 = (i : ℝ) := by exact_mod_cast Nat.sub_add_cancel hi
  have hcN : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by exact_mod_cast Nat.sub_add_cancel hN
  rw [hci, hcN, div_pow, div_pow, one_pow, one_pow] at hs
  have hip : 0 < (i : ℝ) := by exact_mod_cast (show 0 < i by omega)
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hs' := (div_lt_div_iff₀ hip hNp).mp hs
  have hm := mul_le_mul_of_nonneg_left hbranch (le_of_lt hip)
  nlinarith

lemma referenceXi_pos (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ)
    (hi : 1 ≤ i) (hiN : i < N)
    (hbranch : 1 / r ^ N ≤ 1 + (N : ℝ) * (1 + r)) : 0 < referenceXi r i := by
  have h := reference_power_bound r hr hr1 N i hi hiN hbranch
  unfold referenceXi
  exact div_pos (by linarith) (by positivity)

lemma referenceXi_lt_half (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (i : ℕ) (hi : 1 ≤ i) :
    referenceXi r i < (i : ℝ) / 2 := by
  have hip : 0 < (i : ℝ) := by exact_mod_cast (show 0 < i by omega)
  have hri : 1 < 1 / r ^ i := by
    apply (lt_div_iff₀ (by positivity : 0 < r ^ i)).2
    simpa using pow_lt_one₀ (le_of_lt hr) hr1 (by omega : i ≠ 0)
  have hri1 : 1 < 1 / r ^ (i + 1) := by
    apply (lt_div_iff₀ (by positivity : 0 < r ^ (i + 1))).2
    simpa using pow_lt_one₀ (le_of_lt hr) hr1 (by omega : i + 1 ≠ 0)
  unfold referenceXi
  apply (div_lt_iff₀ (by positivity : 0 < (1 + r) * (1 + 1 / r ^ (i + 1)))).2
  have hm := mul_pos hip (show 0 < (1 + r) * (1 / r ^ (i + 1) - 1) by positivity)
  nlinarith

lemma rootPoly_expanded (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (v x : ℝ) (i : ℕ) :
    rootPoly r v i x = pj r (i + 1) * x * (1 + x - (1 - r) / (1 + r))
      + v * (i + 1) * x / (1 + r) - v * (i : ℝ) * (i + 1) / (2 * (1 + r))
      + (1 - r) * PiS r i / (1 + r) := by
  have hp : pj r (i + 1) ≠ 0 := ne_of_gt (pj_pos r hr hr1 (i + 1) (by omega))
  unfold rootPoly
  field_simp [hp]
  ring

lemma referenceXi_quad (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (i : ℕ) :
    rootPoly r (1 + r) i (referenceXi r i) = 0 := by
  have hr2 : 1 - r ^ 2 ≠ 0 := by
    have ht : r ^ 2 < 1 := pow_lt_one₀ (le_of_lt hr) hr1 (by omega)
    linarith
  have hp : pj r (i + 1) ≠ 0 := ne_of_gt (pj_pos r hr hr1 (i + 1) (by omega))
  rw [rootPoly_expanded r hr hr1]
  unfold referenceXi
  rw [PiS_closed r hr hr1 i]
  unfold pj
  have he : r ^ (2 * i) = (r ^ i) ^ 2 := by rw [Nat.mul_comm 2 i, pow_mul]
  have he1 : r ^ (2 * (i + 1)) = (r ^ i * r) ^ 2 := by
    rw [Nat.mul_comm 2 (i + 1), pow_mul, pow_succ r i]
  rw [he, he1, pow_succ r i]
  set b := r ^ i
  have hbpos : 0 < b := pow_pos hr i
  have hbp : 1 - (b * r) ^ 2 ≠ 0 := by
    have ht : r ^ (2 * (i + 1)) < 1 := pow_lt_one₀ (le_of_lt hr) hr1 (by omega)
    rw [he1] at ht
    change (b * r) ^ 2 < 1 at ht
    linarith
  field_simp [hbp]
  ring

lemma rootPoly_parameter (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (v x : ℝ) (i : ℕ) :
    rootPoly r v i x = rootPoly r (1 + r) i x
      + ((1 + r) - v) * (i + 1) / (1 + r) * ((i : ℝ) / 2 - x) := by
  have hp : pj r (i + 1) ≠ 0 := ne_of_gt (pj_pos r hr hr1 (i + 1) (by omega))
  unfold rootPoly
  field_simp [hp]
  ring

lemma rootPoly_actual (r : ℝ) (N i : ℕ) (x : ℝ) :
    rootPoly r (M r N) i x = pj r (i + 1) * x * (1 + x + C r N i) - X r N i := by
  unfold rootPoly C X
  ring

lemma quadratic_root_le (p b X x y : ℝ) (hp : 0 < p) (hX : 0 < X)
    (hx : 0 < x) (hy : 0 ≤ y)
    (hroot : p * x ^ 2 + b * x - X = 0) (hq : 0 ≤ p * y ^ 2 + b * y - X) : x ≤ y := by
  by_contra hle
  have hxy : y - x < 0 := by linarith
  have hpos : 0 < p * x * y + X := by positivity
  have he : x * (p * y ^ 2 + b * y - X) = (y - x) * (p * x * y + X) := by
    linear_combination y * hroot
  have hneg := mul_neg_of_neg_of_pos hxy hpos
  have hnon := mul_nonneg (le_of_lt hx) hq
  rw [he] at hnon
  linarith

lemma quadratic_root_lt (p b X x y : ℝ) (hp : 0 < p) (hX : 0 < X)
    (hx : 0 < x) (hy : 0 ≤ y)
    (hroot : p * x ^ 2 + b * x - X = 0) (hq : 0 < p * y ^ 2 + b * y - X) : x < y := by
  have hle := quadratic_root_le p b X x y hp hX hx hy hroot (le_of_lt hq)
  have hne : x ≠ y := by intro he; subst y; linarith
  exact lt_of_le_of_ne hle hne

lemma rootXi_le_reference (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ)
    (hiN : i < N) (hbranch : 1 / r ^ N ≤ 1 + (N : ℝ) * (1 + r)) :
    rootXi r N i ≤ referenceXi r i := by
  by_cases hi : i = 0
  · subst i; rw [rootXi_zero, referenceXi_zero r hr]
  · have hi1 : 1 ≤ i := by omega
    have hp := pj_pos r hr hr1 (i + 1) (by omega)
    have hx := X_pos r hr hr1 N i hi1 hiN
    have hxi := rootXi_pos r hr hr1 N i hi
    have href := referenceXi_pos r hr hr1 N i hi1 hiN hbranch
    have hm := M_le_h r hr hr1 N (by omega) hbranch
    have hhalf := referenceXi_lt_half r hr hr1 i hi1
    have hpoly : 0 ≤ rootPoly r (M r N) i (referenceXi r i) := by
      rw [rootPoly_parameter r hr hr1, referenceXi_quad r hr hr1, zero_add]
      apply mul_nonneg
      · apply div_nonneg (by positivity) (by positivity)
      · linarith
    rw [rootPoly_actual] at hpoly
    have hroot := rootXi_quad r hr hr1 N i hiN
    unfold eta at hroot
    apply quadratic_root_le (pj r (i + 1)) (pj r (i + 1) * (1 + C r N i)) (X r N i)
      (rootXi r N i) (referenceXi r i) hp hx hxi (le_of_lt href)
    · nlinarith [hroot]
    · nlinarith [hpoly]

lemma rootNu_neg (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (i : ℕ) (hi : 1 ≤ i) : rootNu r i < 0 := by
  have h := pj_slope_strictMono r hr hr1 (by omega : i - 1 < i)
  dsimp at h
  rw [Nat.sub_add_cancel hi] at h
  have hci : ((i - 1 : ℕ) : ℝ) + 1 = (i : ℝ) := by exact_mod_cast Nat.sub_add_cancel hi
  rw [hci] at h
  have hip : 0 < (i : ℝ) := by exact_mod_cast (show 0 < i by omega)
  have hp := pj_pos r hr hr1 i (by omega)
  have hp1 := pj_pos r hr hr1 (i + 1) (by omega)
  have hc := (div_lt_div_iff₀ hip (by positivity)).mp h
  unfold rootNu
  apply sub_neg.mpr
  apply (div_lt_div_iff₀ hp1 hp).2
  nlinarith

lemma pj_strictMono (r : ℝ) (hr : 0 < r) (hr1 : r < 1) : StrictMono (pj r) := by
  have hz : 1 < 1 / r ^ 2 := by
    apply (lt_div_iff₀ (by positivity : 0 < r ^ 2)).2
    simpa using pow_lt_one₀ (le_of_lt hr) hr1 (by omega : 2 ≠ 0)
  intro a b hab
  rw [pj_geometric r (ne_of_gt hr), pj_geometric r (ne_of_gt hr)]
  exact div_lt_div_of_pos_right (sub_lt_sub_right (pow_lt_pow_right₀ hz hab) 1) (by norm_num)

lemma rootE_one (r : ℝ) (hr : 0 < r) : rootE r 1 = (1 + r) * (1 - r) ^ 2 / r := by
  unfold rootE
  norm_num only [pow_one, Nat.cast_one]
  field_simp
  ring

lemma rootE_step (r : ℝ) (hr : 0 < r) (i : ℕ) :
    rootE r (i + 1) - rootE r i = (1 + r) * (1 - r) * (1 / r ^ (i + 1) - 1) := by
  unfold rootE
  push_cast
  rw [pow_succ r i]
  field_simp
  ring

lemma rootE_pos (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (i : ℕ) (hi : 1 ≤ i) : 0 < rootE r i := by
  induction i, hi using Nat.le_induction with
  | base =>
    rw [rootE_one r hr]
    have hd : 0 < 1 - r := by linarith
    positivity
  | succ i hi ih =>
    have hp : 1 < 1 / r ^ (i + 1) := by
      apply (lt_div_iff₀ (pow_pos hr _)).2
      simpa using pow_lt_one₀ (le_of_lt hr) hr1 (by omega : i + 1 ≠ 0)
    have hstep := rootE_step r hr i
    have hg : 0 < (1 + r) * (1 - r) * (1 / r ^ (i + 1) - 1) := by
      have hd : 0 < 1 - r := by linarith
      have hp' : 0 < 1 / r ^ (i + 1) - 1 := by linarith
      positivity
    linarith

lemma rootJ_reference_factor (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (i : ℕ) (hi : 1 ≤ i) :
    rootJ r (1 + r) (referenceXi r (i - 1)) i =
      r ^ i * rootE r i / ((1 - r ^ i) * (1 - (r ^ i * r) ^ 2)) := by
  have hprev : r ^ (i - 1) = r ^ i / r := by
    apply (eq_div_iff (ne_of_gt hr)).2
    rw [← pow_succ, Nat.sub_add_cancel hi]
  have hci : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by
    have hplus : ((i - 1 : ℕ) : ℝ) + 1 = (i : ℝ) := by exact_mod_cast Nat.sub_add_cancel hi
    linarith
  have hpi : pj r i ≠ 0 := ne_of_gt (pj_pos r hr hr1 i (by omega))
  have hpi1 : pj r (i + 1) ≠ 0 := ne_of_gt (pj_pos r hr hr1 (i + 1) (by omega))
  unfold rootJ rootNu referenceXi rootE
  rw [Nat.sub_add_cancel hi, hprev, hci]
  unfold pj
  have he : r ^ (2 * i) = (r ^ i) ^ 2 := by rw [Nat.mul_comm 2 i, pow_mul]
  have he1 : r ^ (2 * (i + 1)) = (r ^ i * r) ^ 2 := by
    rw [Nat.mul_comm 2 (i + 1), pow_mul, pow_succ r i]
  rw [he, he1]
  set b := r ^ i
  have hbpos : 0 < b := pow_pos hr i
  have hblt : b < 1 := pow_lt_one₀ (le_of_lt hr) hr1 (by omega)
  have hbrlt : b * r < 1 := by nlinarith
  have hbrpos : 0 < b * r := by positivity
  have hbnz : 1 - b ≠ 0 := by linarith
  have hbne : 1 - b ^ 2 ≠ 0 := by nlinarith
  have hbrne : 1 - (b * r) ^ 2 ≠ 0 := by nlinarith
  have hbrne' : 1 - b ^ 2 * r ^ 2 ≠ 0 := by convert hbrne using 1 <;> ring
  field_simp [hbnz, hbne, hbrne, hbrne']
  ring

lemma rootJ_reference_pos (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (i : ℕ) (hi : 1 ≤ i) :
    0 < rootJ r (1 + r) (referenceXi r (i - 1)) i := by
  rw [rootJ_reference_factor r hr hr1 i hi]
  have hp : 0 < r ^ i := pow_pos hr i
  have hi1 : r ^ i < 1 := pow_lt_one₀ (le_of_lt hr) hr1 (by omega)
  have hp1 : r ^ i * r < 1 := by nlinarith
  have hp1pos : 0 < r ^ i * r := by positivity
  have hden : 0 < (1 - r ^ i) * (1 - (r ^ i * r) ^ 2) := by
    have hd1 : 0 < 1 - r ^ i := by linarith
    have hd2 : 0 < 1 - (r ^ i * r) ^ 2 := by nlinarith
    positivity
  exact div_pos (mul_pos hp (rootE_pos r hr hr1 i hi)) hden

lemma rootJ_actual_pos (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ)
    (hi : 1 ≤ i) (hiN : i < N)
    (hbranch : 1 / r ^ N ≤ 1 + (N : ℝ) * (1 + r)) :
    0 < rootJ r (M r N) (rootXi r N (i - 1)) i := by
  have href := rootJ_reference_pos r hr hr1 i hi
  have hxi := rootXi_le_reference r hr hr1 N (i - 1) (by omega) hbranch
  have hm := M_le_h r hr hr1 N (by omega) hbranch
  have hnu := rootNu_neg r hr hr1 i hi
  have hpp := pj_strictMono r hr hr1 (by omega : i < i + 1)
  have hp1 := pj_pos r hr hr1 (i + 1) (by omega)
  have hk : 0 < 1 - pj r i / pj r (i + 1) := by
    apply sub_pos.mpr
    exact (div_lt_one hp1).2 hpp
  have hmdiv : M r N / (1 + r) ≤ 1 := (div_le_one (by positivity)).2 hm
  have hnu2 := mul_le_mul_of_nonpos_right hmdiv (le_of_lt hnu)
  have hxi2 := mul_le_mul_of_nonneg_left hxi (le_of_lt hk)
  unfold rootJ at *
  have hh : (1 + r) / (1 + r) = (1 : ℝ) := div_self (by positivity)
  rw [hh] at href
  nlinarith

lemma rootPoly_factor (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ)
    (hi : 1 ≤ i) (hiN : i < N) :
    rootPoly r (M r N) i (pj r i / pj r (i + 1) * (1 + rootXi r N (i - 1))) =
      pj r i * (1 + rootXi r N (i - 1)) * rootJ r (M r N) (rootXi r N (i - 1)) i := by
  have hq := rootXi_quad7 r hr hr1 N (i - 1) (by omega)
  rw [Nat.sub_add_cancel hi] at hq
  have hp : pj r i ≠ 0 := ne_of_gt (pj_pos r hr hr1 i (by omega))
  have hp1 : pj r (i + 1) ≠ 0 := ne_of_gt (pj_pos r hr hr1 (i + 1) (by omega))
  have hci : ((i - 1 : ℕ) : ℝ) + 1 = (i : ℝ) := by exact_mod_cast Nat.sub_add_cancel hi
  rw [rootPoly_actual, ← hq]
  unfold eta C rootJ rootNu
  rw [Nat.sub_add_cancel hi, hci]
  field_simp [hp, hp1]
  ring

lemma rootXi_step_bound (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ)
    (hi : 1 ≤ i) (hiN : i < N)
    (hbranch : 1 / r ^ N ≤ 1 + (N : ℝ) * (1 + r)) :
    rootXi r N i < pj r i / pj r (i + 1) * (1 + rootXi r N (i - 1)) := by
  have hp := pj_pos r hr hr1 (i + 1) (by omega)
  have hpi := pj_pos r hr hr1 i (by omega)
  have hxp := rootXi_pos r hr hr1 N i (by omega)
  have hx := X_pos r hr hr1 N i hi hiN
  have hprev := rootXi_nonneg r hr hr1 N (i - 1)
  have hj := rootJ_actual_pos r hr hr1 N i hi hiN hbranch
  have hy : 0 < pj r i / pj r (i + 1) * (1 + rootXi r N (i - 1)) := by positivity
  have hpoly : 0 < rootPoly r (M r N) i (pj r i / pj r (i + 1) * (1 + rootXi r N (i - 1))) := by
    rw [rootPoly_factor r hr hr1 N i hi hiN]
    positivity
  rw [rootPoly_actual] at hpoly
  have hroot := rootXi_quad r hr hr1 N i hiN
  unfold eta at hroot
  apply quadratic_root_lt (pj r (i + 1)) (pj r (i + 1) * (1 + C r N i)) (X r N i)
    (rootXi r N i) (pj r i / pj r (i + 1) * (1 + rootXi r N (i - 1))) hp hx hxp (le_of_lt hy)
  · nlinarith [hroot]
  · nlinarith [hpoly]

lemma Abar_root_pos (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ) :
    0 < Abar (rootXi r N) i := by
  induction i with
  | zero => simp [Abar]
  | succ i ih =>
    rw [Abar]
    have hx := rootXi_pos r hr hr1 N (i + 1) (by omega)
    have hp := rootXi_nonneg r hr hr1 N i
    exact div_pos (mul_pos ih (by linarith)) hx

lemma Abar_root_recur (r : ℝ) (N i : ℕ) (hi : 1 ≤ i) :
    Abar (rootXi r N) i = Abar (rootXi r N) (i - 1) *
      (1 + rootXi r N (i - 1)) / rootXi r N i := by
  have he : i - 1 + 1 = i := Nat.sub_add_cancel hi
  conv_lhs => rw [← he]
  rw [Abar, he]

lemma rootXi_step_scaled (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ)
    (hi : 1 ≤ i) (hiN : i < N)
    (hbranch : 1 / r ^ N ≤ 1 + (N : ℝ) * (1 + r)) :
    pj r (i + 1) * rootXi r N i < pj r i * (1 + rootXi r N (i - 1)) := by
  have h := rootXi_step_bound r hr hr1 N i hi hiN hbranch
  have hp := pj_pos r hr hr1 (i + 1) (by omega)
  have hm := mul_lt_mul_of_pos_left h hp
  have he : pj r (i + 1) * (pj r i / pj r (i + 1) * (1 + rootXi r N (i - 1))) =
      pj r i * (1 + rootXi r N (i - 1)) := by field_simp
  rwa [he] at hm

lemma Abar_root_step (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ)
    (hi : 1 ≤ i) (hiN : i < N)
    (hbranch : 1 / r ^ N ≤ 1 + (N : ℝ) * (1 + r)) :
    Abar (rootXi r N) (i - 1) < Abar (rootXi r N) i := by
  have hx := rootXi_pos r hr hr1 N i (by omega)
  have hprev := rootXi_nonneg r hr hr1 N (i - 1)
  have hA := Abar_root_pos r hr hr1 N (i - 1)
  have hsc := rootXi_step_scaled r hr hr1 N i hi hiN hbranch
  have hpp := pj_strictMono r hr hr1 (by omega : i < i + 1)
  have hp := pj_pos r hr hr1 i (by omega)
  have hmult := mul_lt_mul_of_pos_right hpp hx
  have hless : rootXi r N i < 1 + rootXi r N (i - 1) := by
    have h0 : pj r i * rootXi r N i < pj r i * (1 + rootXi r N (i - 1)) := by linarith
    exact (mul_lt_mul_iff_right₀ hp).mp h0
  rw [Abar_root_recur r N i hi]
  apply (lt_div_iff₀ hx).2
  exact mul_lt_mul_of_pos_left hless hA

lemma D_root_pos (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N j : ℕ)
    (hj : 1 ≤ j) (hjN : j ≤ N) : 0 < D r (rootXi r N) N j := by
  simp only [D, if_neg (by omega : ¬(j = 0 ∨ N < j)), Am, if_neg (by omega : j ≠ 0)]
  exact div_pos (pj_pos r hr hr1 j (by omega)) (Abar_root_pos r hr hr1 N (j - 1))

lemma D_root_nonneg (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N j : ℕ) :
    0 ≤ D r (rootXi r N) N j := by
  by_cases h : j = 0 ∨ N < j
  · simp [D, h]
  · exact le_of_lt (D_root_pos r hr hr1 N j (by omega) (by omega))

lemma D_root_step (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ)
    (hi : 1 ≤ i) (hiN : i < N)
    (hbranch : 1 / r ^ N ≤ 1 + (N : ℝ) * (1 + r)) :
    D r (rootXi r N) N (i + 1) < D r (rootXi r N) N i := by
  have hA := Abar_root_pos r hr hr1 N i
  have hAp := Abar_root_pos r hr hr1 N (i - 1)
  have hx := rootXi_pos r hr hr1 N i (by omega)
  have hsc := rootXi_step_scaled r hr hr1 N i hi hiN hbranch
  have hscA := mul_lt_mul_of_pos_right hsc hAp
  have hrec : Abar (rootXi r N) i * rootXi r N i =
      Abar (rootXi r N) (i - 1) * (1 + rootXi r N (i - 1)) := by
    rw [Abar_root_recur r N i hi, div_mul_cancel₀ _ (ne_of_gt hx)]
  have hmain : pj r (i + 1) * Abar (rootXi r N) (i - 1) < pj r i * Abar (rootXi r N) i := by
    apply (mul_lt_mul_iff_right₀ hx).mp
    calc
      _ = pj r (i + 1) * rootXi r N i * Abar (rootXi r N) (i - 1) := by ring
      _ < pj r i * (1 + rootXi r N (i - 1)) * Abar (rootXi r N) (i - 1) := hscA
      _ = _ := by linear_combination -pj r i * hrec
  simp only [D, if_neg (by omega : ¬(i + 1 = 0 ∨ N < i + 1)),
    if_neg (by omega : ¬(i = 0 ∨ N < i)), Am, if_neg (by omega : i + 1 ≠ 0),
    if_neg (by omega : i ≠ 0), Nat.add_sub_cancel]
  exact (div_lt_div_iff₀ hA hAp).2 hmain

lemma ell_root_nonneg (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i j : ℕ)
    (hiN : i ≤ N) (hjN : j ≤ N) (hij : i ≠ j)
    (hbranch : 1 / r ^ N ≤ 1 + (N : ℝ) * (1 + r)) :
    0 ≤ ell r (rootXi r N) N i j := by
  have hA : ∀ a, a < N → 0 ≤ Abar (rootXi r N) a - Am (rootXi r N) a := by
    intro a ha
    by_cases h0 : a = 0
    · subst a; simp [Abar, Am]
    · simp only [Am, if_neg h0]
      exact le_of_lt (sub_pos.mpr (Abar_root_step r hr hr1 N a (by omega) ha hbranch))
  have hD : ∀ b, 1 ≤ b → b ≤ N → 0 ≤ D r (rootXi r N) N b - D r (rootXi r N) N (b + 1) := by
    intro b hb hbN
    by_cases he : b = N
    · subst b
      have hn1 : D r (rootXi r N) N (N + 1) = 0 := by simp [D]
      rw [hn1, sub_zero]
      exact D_root_nonneg r hr hr1 N N
    · exact le_of_lt (sub_pos.mpr (D_root_step r hr hr1 N b hb (by omega) hbranch))
  unfold ell
  by_cases h : i < j
  · rw [if_pos h]
    apply mul_nonneg (hA i (by omega))
    exact add_nonneg (D_root_nonneg r hr hr1 N j)
      (mul_nonneg (le_of_lt hr) (D_root_nonneg r hr hr1 N (j + 1)))
  · rw [if_neg h]
    have hji : j < i := by omega
    apply mul_nonneg _ (hD i (by omega) hiN)
    apply add_nonneg
    · unfold Am; split_ifs
      · exact le_rfl
      · exact le_of_lt (Abar_root_pos r hr hr1 N (j - 1))
    · exact mul_nonneg (le_of_lt hr) (le_of_lt (Abar_root_pos r hr hr1 N j))

lemma M_boundary (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N : ℕ) (hN : 1 ≤ N)
    (hboundary : 1 / r ^ N = 1 + (N : ℝ) * (1 + r)) : M r N = 1 + r := by
  have he : 1 / r ^ (2 * N) = (1 / r ^ N) ^ 2 := by
    rw [Nat.mul_comm 2 N, pow_mul, div_pow, one_pow]
  have h := M_gap r hr hr1 N hN
  rw [he, hboundary, sub_self, zero_div] at h
  linarith

lemma inverse_power_boundary (r : ℝ) (hr : 0 < r) (N : ℕ)
    (hboundary : 1 / r ^ N = 1 + (N : ℝ) * (1 + r)) :
    r ^ (-(2 * (N : ℤ))) = (1 + (N : ℝ) * (1 + r)) ^ 2 := by
  rw [zpow_neg]
  have he : (2 * (N : ℤ)) = ((2 * N : ℕ) : ℤ) := by simp
  rw [he, zpow_natCast, Nat.mul_comm 2 N, pow_mul]
  have hd : ((r ^ N) ^ 2)⁻¹ = (1 / r ^ N) ^ 2 := by rw [div_pow, one_pow, one_div]
  rw [hd, hboundary]

lemma internal_sum_nonneg (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N : ℕ)
    (hbranch : 1 / r ^ N ≤ 1 + (N : ℝ) * (1 + r)) (f : ℕ → ℝ) (P : ℕ → ℕ → ℝ)
    (hQ : ∀ i j, i ≤ N → j ≤ N → i ≠ j → 0 ≤ Qv (1 + r) f P i j) :
    0 ≤ 2 * (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1),
      if i = j then 0 else ell r (rootXi r N) N i j * Qv (1 + r) f P i j) := by
  apply mul_nonneg (by norm_num)
  apply sum_nonneg; intro i hi
  apply sum_nonneg; intro j hj
  by_cases hij : i = j
  · simp [hij]
  · rw [if_neg hij]
    exact mul_nonneg
      (ell_root_nonneg r hr hr1 N i j (by simpa using hi) (by simpa using hj) hij hbranch)
      (hQ i j (by simpa using hi) (by simpa using hj) hij)

lemma optimal_history_identity (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N : ℕ) (hN : 1 ≤ N)
    (hboundary : 1 / r ^ N = 1 + (N : ℝ) * (1 + r))
    (f : ℕ → ℝ) (P : ℕ → ℕ → ℝ) (hP : ∀ i j, P i j = P j i) :
    (1 + r) * smallK N (1 + r) f (fun i => P i i) =
      2 * (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1),
        if i = j then 0 else ell r (rootXi r N) N i j * Qv (1 + r) f P i j) := by
  have h := internal_reduction r N hN (rootXi r N) hr hr1
    (fun i hi => rootXi_pos r hr hr1 N i hi) (rootXi_zero r N)
    (fun i hi => rootXi_quad r hr hr1 N i hi)
    (fun i hi => rootXi_quad7 r hr hr1 N i hi) (rootXi_pin r hr hr1 N hN) f P hP
  rw [h, M_boundary r hr hr1 N hN hboundary, inverse_power_boundary r hr N hboundary]
  unfold smallK
  ring

theorem optimal_history_nonneg (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N : ℕ) (hN : 1 ≤ N)
    (hboundary : 1 / r ^ N = 1 + (N : ℝ) * (1 + r))
    (f : ℕ → ℝ) (P : ℕ → ℕ → ℝ) (hP : ∀ i j, P i j = P j i)
    (hQ : ∀ i j, i ≤ N → j ≤ N → i ≠ j → 0 ≤ Qv (1 + r) f P i j) :
    0 ≤ smallK N (1 + r) f (fun i => P i i) := by
  have hn := internal_sum_nonneg r hr hr1 N (le_of_eq hboundary) f P hQ
  rw [← optimal_history_identity r hr hr1 N hN hboundary f P hP] at hn
  by_contra hk
  have hneg := mul_neg_of_pos_of_neg (show 0 < 1 + r by positivity) (lt_of_not_ge hk)
  linarith

lemma interpolation_scaling (a s h : ℝ) (he : h = s * a) (f : ℕ → ℝ) (P : ℕ → ℕ → ℝ) (i j : ℕ) :
    Qv a (fun k => s * f k) (fun k l => s ^ 2 * P k l) i j =
      s * Qv h f P i j + s * (1 - s) / 2 * (P i i + P j j - 2 * P i j) := by
  unfold Qv ginner
  simp only [← mul_sum]
  rw [he]
  ring

lemma ginner_forward (h : ℝ) (P : ℕ → ℕ → ℝ) (i : ℕ) : ginner h P i (i + 1) = h * P (i + 1) i := by
  unfold ginner
  rw [sum_range_succ]
  ring

lemma ginner_backward (h : ℝ) (P : ℕ → ℕ → ℝ) (i : ℕ) : ginner h P (i + 1) i = -h * P i i := by
  unfold ginner
  rw [sum_range_succ]
  ring

lemma adjacent_interpolation_sum (h : ℝ) (f : ℕ → ℝ) (P : ℕ → ℕ → ℝ)
    (hP : ∀ i j, P i j = P j i) (i : ℕ) :
    2 * (Qv h f P i (i + 1) + Qv h f P (i + 1) i) =
      h * (P i i - P (i + 1) (i + 1))
        - (2 - h) * (P i i + P (i + 1) (i + 1) - 2 * P i (i + 1)) := by
  unfold Qv
  rw [ginner_forward, ginner_backward, hP (i + 1) i]
  ring

lemma gradient_square_step (h : ℝ) (hh : 0 < h) (hh2 : h ≤ 2)
    (f : ℕ → ℝ) (P : ℕ → ℕ → ℝ) (hP : ∀ i j, P i j = P j i) (i : ℕ)
    (hQf : 0 ≤ Qv h f P i (i + 1)) (hQb : 0 ≤ Qv h f P (i + 1) i)
    (hdiff : 0 ≤ P i i + P (i + 1) (i + 1) - 2 * P i (i + 1)) :
    P (i + 1) (i + 1) ≤ P i i := by
  have he := adjacent_interpolation_sum h f P hP i
  have hnon := mul_nonneg (show 0 ≤ 2 - h by linarith) hdiff
  have hm : 0 ≤ h * (P i i - P (i + 1) (i + 1)) := by linarith
  by_contra hneg
  have hn := mul_neg_of_pos_of_neg hh (show P i i - P (i + 1) (i + 1) < 0 by linarith)
  linarith

lemma decreasing_sequence_tail (q : ℕ → ℝ) (N : ℕ)
    (hstep : ∀ i, i < N → q (i + 1) ≤ q i) (i : ℕ) (hi : i ≤ N) : q N ≤ q i := by
  have hchain : ∀ j, i ≤ j → j ≤ N → q j ≤ q i := by
    intro j hij
    induction j, hij using Nat.le_induction with
    | base => intro h; exact le_rfl
    | succ j hij ih =>
      intro hjN
      exact le_trans (hstep j (by omega)) (ih (by omega))
  exact hchain N hi le_rfl

lemma scaled_history_identity (N : ℕ) (a s : ℝ) (f q : ℕ → ℝ) :
    smallK N a (fun i => s * f i) (fun i => s ^ 2 * q i) = s * scaledK N a s f q := by
  unfold smallK scaledK
  simp only [mul_sub, sum_sub_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul]
  ring

lemma small_history_split (N : ℕ) (a s h : ℝ) (he : h = s * a) (f q : ℕ → ℝ) :
    smallK N h f q = scaledK N a s f q
      + (1 - s) * ((∑ i ∈ range N, q i) - (N : ℝ) * q N) := by
  unfold smallK scaledK
  rw [he]
  ring

theorem small_history_nonneg
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N : ℕ) (hN : 1 ≤ N)
    (hboundary : 1 / r ^ N = 1 + (N : ℝ) * (1 + r))
    (h : ℝ) (hh : 0 < h) (hha : h ≤ 1 + r)
    (f : ℕ → ℝ) (P : ℕ → ℕ → ℝ) (hP : ∀ i j, P i j = P j i)
    (hQ : ∀ i j, i ≤ N → j ≤ N → i ≠ j → 0 ≤ Qv h f P i j)
    (hdiff : ∀ i j, i ≤ N → j ≤ N → 0 ≤ P i i + P j j - 2 * P i j) :
    0 ≤ smallK N h f (fun i => P i i) := by
  let s := h / (1 + r)
  have hs : 0 < s := div_pos hh (by positivity)
  have hs1 : s ≤ 1 := (div_le_one (by positivity)).2 hha
  have he : h = s * (1 + r) := by dsimp [s]; field_simp
  have hPs : ∀ i j, s ^ 2 * P i j = s ^ 2 * P j i := by intro i j; rw [hP]
  have hQs : ∀ i j, i ≤ N → j ≤ N → i ≠ j →
      0 ≤ Qv (1 + r) (fun i => s * f i) (fun i j => s ^ 2 * P i j) i j := by
    intro i j hi hj hij
    rw [interpolation_scaling (1 + r) s h he]
    exact add_nonneg (mul_nonneg (le_of_lt hs) (hQ i j hi hj hij))
      (mul_nonneg (by positivity) (hdiff i j hi hj))
  have hk := optimal_history_nonneg r hr hr1 N hN hboundary
    (fun i => s * f i) (fun i j => s ^ 2 * P i j) hPs hQs
  rw [scaled_history_identity] at hk
  have hks : 0 ≤ scaledK N (1 + r) s f (fun i => P i i) := by
    by_contra hneg
    have hn := mul_neg_of_pos_of_neg hs (lt_of_not_ge hneg)
    linarith
  have hstep : ∀ i, i < N → P (i + 1) (i + 1) ≤ P i i := by
    intro i hi
    exact gradient_square_step h hh (by linarith) f P hP i
      (hQ i (i + 1) (by omega) (by omega) (by omega))
      (hQ (i + 1) i (by omega) (by omega) (by omega)) (hdiff i (i + 1) (by omega) (by omega))
  have hsum : 0 ≤ (∑ i ∈ range N, P i i) - (N : ℝ) * P N N := by
    have ht : 0 ≤ ∑ i ∈ range N, (P i i - P N N) := by
      apply sum_nonneg; intro i hi
      exact sub_nonneg.mpr (decreasing_sequence_tail (fun i => P i i) N hstep i (le_of_lt (mem_range.mp hi)))
    simpa only [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul] using ht
  rw [small_history_split N (1 + r) s h he]
  exact add_nonneg hks (mul_nonneg (by linarith) hsum)

lemma small_step_identity (N : ℕ) (h : ℝ) (f : ℕ → ℝ) (P : ℕ → ℕ → ℝ) (R : ℕ → ℝ)
    (X0 XN : ℝ) (hP : ∀ i j, P i j = P j i)
    (htrajectory : XN = X0 - 2 * h * (∑ i ∈ range N, R i)
      + h ^ 2 * (∑ i ∈ range N, ∑ j ∈ range N, P i j)) :
    h * smallK N h f (fun i => P i i)
      + 2 * h * (∑ i ∈ range N, (-f i + gself h R P i - (1 / 2) * P i i)) =
      X0 - XN - 2 * (N : ℝ) * h * f N - (N : ℝ) * h * (1 + (N : ℝ) * h) * P N N := by
  rw [htrajectory]
  unfold smallK gself
  simp only [sum_sub_distrib, sum_add_distrib, sum_neg_distrib, ← mul_sum,
    sum_const, card_range, nsmul_eq_mul]
  have hs := symmetric_square_telescope P hP N
  linear_combination -h ^ 2 * hs

end GDGen3Proof_small_step_square_bound

open GDGen3Proof_small_step_square_bound

theorem solution
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N : ℕ) (hN : 1 ≤ N)
    (hboundary : 1 / r ^ N = 1 + (N : ℝ) * (1 + r))
    (h : ℝ) (hh : 0 < h) (hha : h ≤ 1 + r)
    (f : ℕ → ℝ) (P : ℕ → ℕ → ℝ) (R : ℕ → ℝ) (X0 XN : ℝ)
    (hP : ∀ i j, P i j = P j i)
    (hQ : ∀ i j, i ≤ N → j ≤ N → i ≠ j → 0 ≤ Qv h f P i j)
    (hdiff : ∀ i j, i ≤ N → j ≤ N → 0 ≤ P i i + P j j - 2 * P i j)
    (hstar : ∀ i, i < N → 0 ≤ -f i + gself h R P i - (1 / 2) * P i i)
    (hfN : (1 / 2) * P N N ≤ f N) (hXN : P N N ≤ XN)
    (htrajectory : XN = X0 - 2 * h * (∑ i ∈ range N, R i)
      + h ^ 2 * (∑ i ∈ range N, ∑ j ∈ range N, P i j)) :
    (1 + (N : ℝ) * h) ^ 2 * P N N ≤ X0 := by
  have hk := small_history_nonneg r hr hr1 N hN hboundary h hh hha f P hP hQ hdiff
  have hs : 0 ≤ ∑ i ∈ range N, (-f i + gself h R P i - (1 / 2) * P i i) := by
    apply sum_nonneg; intro i hi; exact hstar i (mem_range.mp hi)
  have he := small_step_identity N h f P R X0 XN hP htrajectory
  have hl : 0 ≤ h * smallK N h f (fun i => P i i) +
      2 * h * (∑ i ∈ range N, (-f i + gself h R P i - (1 / 2) * P i i)) := by positivity
  have hf := mul_le_mul_of_nonneg_left hfN (show 0 ≤ 2 * (N : ℝ) * h by positivity)
  nlinarith [he, hl, hf]
