-- Prove2me | solution 1 for BadLocalMin.Smooth.constant_output_eq_20_21
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:48:27.571879+00:00
-- url     : https://prove2.me/submissions/4ecc25e6-fe16-44fd-a89c-4864da19d561

import Mathlib
import Definitions.Def_BadLocalMin_Smooth_Model

open BadLocalMin.Smooth in
theorem solution (H N : ℕ) (d : ℕ → ℕ) (σ : ℝ → ℝ)
    (X : Fin (d 0) → Fin N → ℝ) (a : ℝ) (θ : Params d H) (hθ : Constr19ad σ a θ) :
    (∀ (k : ℕ) (hk : k < H) (i : Fin (d (k + 1))) (n : Fin N),
        (∑ j, θ.1 ⟨k, by omega⟩ i j * post σ X θ k (by omega) j n) + θ.2 ⟨k, hk⟩ i = a) ∧
    (∀ (k : ℕ) (hk1 : 1 ≤ k) (hkH : k ≤ H) (i : Fin (d k)) (n : Fin N),
        post σ X θ k hkH i n = σ a) ∧
      (Constr19e θ → 1 ≤ d H → ∀ i n, output σ X θ i n = σ a) := by
  obtain ⟨h0, hb0, hk⟩ := hθ
  have A : ∀ (k : ℕ) (hk : k < H) (i : Fin (d (k + 1))) (n : Fin N),
      (∑ j, θ.1 ⟨k, by omega⟩ i j * post σ X θ k (by omega) j n) + θ.2 ⟨k, hk⟩ i = a := by
    intro k
    induction k with
    | zero =>
      intro hk' i n
      simp only [h0 i, zero_mul, Finset.sum_const_zero, zero_add]
      exact hb0 hk' i
    | succ k ih =>
      intro hk' i n
      have hpost : ∀ j, post σ X θ (k + 1) (by omega) j n = σ a := by
        intro j
        show σ ((∑ j', θ.1 ⟨k, by omega⟩ j j' * post σ X θ k (by omega) j' n) + θ.2 ⟨k, by omega⟩ j) = σ a
        rw [ih (by omega) j n]
      simp only [hpost]
      rw [(hk (k + 1) hk' (by omega) i).2, ← Finset.sum_mul]
      ring
  have B : ∀ (k : ℕ) (hk1 : 1 ≤ k) (hkH : k ≤ H) (i : Fin (d k)) (n : Fin N),
      post σ X θ k hkH i n = σ a := by
    intro k hk1 hkH i n
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    show σ ((∑ j', θ.1 ⟨k', by omega⟩ i j' * post σ X θ k' (by omega) j' n) + θ.2 ⟨k', by omega⟩ i) = σ a
    rw [A k' (by omega) i n]
  refine ⟨A, B, ?_⟩
  intro he hd i n
  rcases Nat.eq_zero_or_pos H with hH | hH
  · subst hH
    exfalso
    have j0 : Fin (d 0) := ⟨0, by omega⟩
    have e1 := he i j0
    have e2 := h0 i j0
    have e3 : (1 : ℝ) / (d 0 : ℝ) = 0 := e1.symm.trans e2
    have : (0 : ℝ) < 1 / (d 0 : ℝ) := by
      have : (1 : ℝ) ≤ (d 0 : ℝ) := by exact_mod_cast hd
      positivity
    linarith
  · unfold output
    have hp : ∀ j, post σ X θ H le_rfl j n = σ a := fun j => B H hH le_rfl j n
    simp only [hp, he i, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Fin.val_last]
    have : (d H : ℝ) ≠ 0 := by
      have : (1 : ℝ) ≤ (d H : ℝ) := by exact_mod_cast hd
      positivity
    field_simp
