-- Prove2me | solution 1 for GDGen3.certificate_identity_general
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:25:28.636734+00:00
-- url     : https://prove2.me/submissions/52a73bd4-4a36-4345-bf8b-d9a3804c3f3e

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

open GDGen3

namespace GDGen3Proof_certificate_identity_general

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

end GDGen3Proof_certificate_identity_general

open GDGen3Proof_certificate_identity_general

theorem solution
    (r : ℝ) (N : ℕ) (hN : 1 ≤ N) (ξ : ℕ → ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hpos : ∀ i : ℕ, i ≠ 0 → 0 < ξ i) (h0 : ξ 0 = 0)
    (hquad : ∀ i : ℕ, i < N → pj r (i + 1) * ξ i * (1 + eta r N ξ i) = X r N i)
    (hquad7 : ∀ i : ℕ, i < N → pj r (i + 1) * eta r N ξ i * (1 + ξ i) = X r N (i + 1))
    (hpin : pj r N * ξ (N - 1) = X r N (N - 1))
    (f : ℕ → ℝ) (P : ℕ → ℕ → ℝ) (R : ℕ → ℝ) (X0 : ℝ)
    (hP : ∀ i j, P i j = P j i) :
    certSum r N ξ f P R = certRhs r N P R X0 := by
  have hin := internal_reduction r N hN ξ hr hr1 hpos h0 hquad hquad7 hpin f P hP
  have hfac : (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1),
      if i = j then 0 else 2 * r ^ (2 * N) * ell r ξ N i j * Qv (1 + r) f P i j) =
      r ^ (2 * N) * (2 * ∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1),
        if i = j then 0 else ell r ξ N i j * Qv (1 + r) f P i j) := by
    simp only [mul_sum]
    apply sum_congr rfl; intro i hi
    apply sum_congr rfl; intro j hj
    split_ifs <;> ring
  have ht : ∀ i,
      2 * (1 + r) * r ^ (2 * N) * (-f i + gself (1 + r) R P i - (1 / 2) * P i i)
        + 2 * r ^ (2 * N) * ((1 + r) - M r N) * (f i - (1 / 2) * P i i) =
      -2 * r ^ (2 * N) * M r N * f i + 2 * (1 + r) * r ^ (2 * N) * R i
        - 2 * (1 + r) ^ 2 * r ^ (2 * N) * (∑ j ∈ range i, P i j)
        - r ^ (2 * N) * (2 * (1 + r) - M r N) * P i i := by
    intro i; unfold gself; ring
  have hpow : r ^ (2 * N) * r ^ (-(2 * (N : ℤ))) = 1 := by
    rw [zpow_neg]
    have he : (2 * (N : ℤ)) = ((2 * N : ℕ) : ℤ) := by simp
    rw [he, zpow_natCast]
    exact mul_inv_cancel₀ (pow_ne_zero _ (ne_of_gt hr))
  have hsq := symmetric_square_telescope P hP N
  unfold certSum certRhs
  rw [hfac, hin]
  simp only [ht, gself, sum_sub_distrib, sum_add_distrib, sum_neg_distrib, ← mul_sum,
    sum_const, card_range, nsmul_eq_mul]
  linear_combination -(1 + r) ^ 2 * r ^ (2 * N) * hsq - P N N * hpow


/-! ## Section 3: explicit roots and multiplier positivity -/
