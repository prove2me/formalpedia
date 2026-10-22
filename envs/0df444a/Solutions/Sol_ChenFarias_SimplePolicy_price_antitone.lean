-- Prove2me | solution 1 for ChenFarias.SimplePolicy.price_antitone
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:29:29.866803+00:00
-- url     : https://prove2.me/submissions/2a94dcaa-f440-433e-8669-84e6ba7ef8de

import Mathlib
import Definitions.Def_ChenFarias_SimplePolicy_Model
set_option autoImplicit false

open ChenFarias.SimplePolicy

lemma cf_Fbar_nonneg (f : ℝ → ℝ) (hf : Assumption1 f) (p : ℝ) : 0 ≤ Fbar f p :=
  MeasureTheory.setIntegral_nonneg measurableSet_Ioi (fun v _ => hf.nonnegative v)

lemma cf_term_le (lam β : ℝ) (f : ℝ → ℝ) (V : ℕ → ℝ) (hV : IsValueFn lam β f V)
    (x : ℕ) (hx : 1 ≤ x) (p : ℝ) (hp : 0 ≤ p) :
    lam * Fbar f p * (p + V (x - 1) - V x) ≤ β * V x :=
  (hV.2 x hx).1 ⟨p, hp, rfl⟩

lemma cf_lub (lam β : ℝ) (f : ℝ → ℝ) (V : ℕ → ℝ) (hV : IsValueFn lam β f V)
    (x : ℕ) (hx : 1 ≤ x) (b : ℝ)
    (hb : ∀ p : ℝ, 0 ≤ p → lam * Fbar f p * (p + V (x - 1) - V x) ≤ b) : β * V x ≤ b :=
  (hV.2 x hx).2 (by rintro y ⟨p, hp, rfl⟩; exact hb p hp)

lemma cf_mono (lam β : ℝ) (f : ℝ → ℝ) (V : ℕ → ℝ)
    (hlam : 0 < lam) (hβ : 0 < β) (hf : Assumption1 f) (hV : IsValueFn lam β f V) :
    ∀ n : ℕ, V n ≤ V (n + 1) := by
  intro n
  induction n with
  | zero =>
    by_contra h
    push_neg at h
    have h1 := cf_term_le lam β f V hV 1 le_rfl 0 le_rfl
    have h0 : V 0 = 0 := hV.1
    have h2 : 0 ≤ lam * Fbar f 0 := mul_nonneg hlam.le (cf_Fbar_nonneg f hf 0)
    simp only [Nat.sub_self, h0] at h1 h
    nlinarith
  | succ n ih =>
    by_contra h
    push_neg at h
    have key : β * V (n + 1) ≤ β * V (n + 1 + 1) := by
      apply cf_lub lam β f V hV (n + 1) (by omega)
      intro p hp
      have h3 := cf_term_le lam β f V hV (n + 1 + 1) (by omega) p hp
      simp only [Nat.add_sub_cancel] at h3 ⊢
      have h4 : 0 ≤ lam * Fbar f p := mul_nonneg hlam.le (cf_Fbar_nonneg f hf p)
      have h5 : lam * Fbar f p * (p + V n - V (n + 1)) ≤ lam * Fbar f p * (p + V (n + 1) - V (n + 1 + 1)) :=
        mul_le_mul_of_nonneg_left (by linarith) h4
      linarith
    have := le_of_mul_le_mul_left key hβ
    linarith

lemma cf_concave (lam β : ℝ) (f : ℝ → ℝ) (V : ℕ → ℝ)
    (hlam : 0 < lam) (hβ : 0 < β) (hf : Assumption1 f) (hV : IsValueFn lam β f V) :
    ∀ n : ℕ, 1 ≤ n → V (n + 1) - V n ≤ V n - V (n - 1) := by
  intro n hn
  by_contra h
  push_neg at h
  have key : β * V (n + 1) ≤ β * V n := by
    apply cf_lub lam β f V hV (n + 1) (by omega)
    intro p hp
    have h3 := cf_term_le lam β f V hV n hn p hp
    simp only [Nat.add_sub_cancel] at ⊢
    have h4 : 0 ≤ lam * Fbar f p := mul_nonneg hlam.le (cf_Fbar_nonneg f hf p)
    have h5 : lam * Fbar f p * (p + V n - V (n + 1)) ≤ lam * Fbar f p * (p + V (n - 1) - V n) :=
      mul_le_mul_of_nonneg_left (by linarith) h4
    linarith
  have h6 := le_of_mul_le_mul_left key hβ
  have h7 := cf_mono lam β f V hlam hβ hf hV n
  have h8 := cf_mono lam β f V hlam hβ hf hV (n - 1)
  have : n - 1 + 1 = n := by omega
  rw [this] at h8
  linarith

lemma cf_dantitone (lam β : ℝ) (f : ℝ → ℝ) (V : ℕ → ℝ)
    (hlam : 0 < lam) (hβ : 0 < β) (hf : Assumption1 f) (hV : IsValueFn lam β f V) :
    ∀ k x : ℕ, 1 ≤ x → V (x + k) - V (x + k - 1) ≤ V x - V (x - 1) := by
  intro k
  induction k with
  | zero => intro x hx; simp
  | succ k ih =>
    intro x hx
    have h1 := cf_concave lam β f V hlam hβ hf hV (x + k) (by omega)
    have h2 := ih x hx
    have : x + (k + 1) = x + k + 1 := by omega
    rw [this]
    simp only [Nat.add_sub_cancel]
    linarith

theorem solution (lam β : ℝ) (f : ℝ → ℝ) (V : ℕ → ℝ) (π : ℕ → ℝ)
    (hlam : 0 < lam) (hβ : 0 < β) (hf : Assumption1 f)
    (hV : IsValueFn lam β f V) (hπ : IsRootPolicy f V π) :
    AntitoneOn π (Set.Ici 1) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ici] at hx hy
  by_contra h
  push_neg at h
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hxy
  have hd := cf_dantitone lam β f V hlam hβ hf hV k x hx
  obtain ⟨hx0, hxr, hxu⟩ := hπ x hx
  obtain ⟨hy0, hyr, hyu⟩ := hπ (x + k) hy
  have hm := hf.virtual_monotone (show π x ∈ Set.Ici (0:ℝ) from hx0) (show π (x + k) ∈ Set.Ici (0:ℝ) from hy0) h.le
  have heq : psi f (π (x + k)) = V x - V (x - 1) := by linarith
  have := hxu _ hy0 heq
  linarith
