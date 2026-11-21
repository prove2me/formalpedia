-- Prove2me | solution 1 for Corless.fold_of_mod4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:45:06.548963+00:00
-- url     : https://prove2.me/submissions/6b5153eb-cd5d-4b6f-8b4a-0366512ec347

module
public import Mathlib.Algebra.BigOperators.Intervals
public import Definitions.Def_LeanPool_CorlessNilpotent_Parity
public import Definitions.Def_LeanPool_CorlessNilpotent_Main
public import Theorems.Thm_Corless_Dv_sub_mod4
public import Theorems.Thm_Corless_indep
public import Theorems.Thm_Corless_Dv_one
public import Theorems.Thm_Corless_Dv_star
public import Theorems.Thm_Corless_Dv_zero
public import Theorems.Thm_Corless_f_pow_two
public import Theorems.Thm_Corless_folded_sizes
public import Theorems.Thm_Corless_isSign_star
public import Theorems.Thm_Corless_two_eq_zero_Z2X
attribute [local simp] Corless.Dv_one
attribute [local simp] Corless.Dv_zero



set_option autoImplicit true
@[expose] public section
public section
open Polynomial Finset
open Corless
namespace Corless
theorem _root_.solution (k : ℕ) {s : ℕ → ℤ} (hs : IsSign s (2 ^ (k + 2) - 1))
    (h : ∃ R : ℤ[X], Dv s (2 ^ (k + 2) - 1) = 1 + 4 * R) :
    IsFolded s (2 ^ (k + 1) - 2) := by
  set n := 2 ^ (k + 1) - 2
  obtain ⟨hN, hM⟩ : 2 ^ (k + 1) - 1 = n + 1 ∧ 2 ^ (k + 2) - 1 = 2 * n + 3 :=
    folded_sizes k
  rw [hM] at h hs
  obtain ⟨R, hR⟩ := h
  -- D(star) ≡ 1 (mod 4)
  obtain ⟨A, hA⟩ := f_pow_two k
  rw [hN] at hA
  have hstar : Dv (star n) (2 * n + 3) = 1 + 4 * (A + A ^ 2) := by
    rw [Dv_star, hA]; ring
  -- the halved differences
  let δ : ℕ → ℤ := fun j => (s j - star n j) / 2
  have hδ : ∀ j, j + 1 < 2 * n + 3 → s j - star n j = 2 * δ j := by
    intro j hj
    simp only [δ]
    by_cases h2 : j = n + 1
    · subst h2
      rcases hs (n + 1) hj with h1 | h1 <;> simp [star, h1]
    · rcases hs j hj with h1 | h1 <;> simp [star, h1, h2]
  obtain ⟨R', hR'⟩ := Dv_sub_mod4 hs (isSign_star n _) δ hδ
  rw [hR, hstar, show 2 * n + 3 - 1 = 2 * (n + 1) by omega] at hR'
  -- divide by 2 and reduce modulo 2
  have hsum2 : ∑ j ∈ range (2 * (n + 1)), C (δ j) * X * f j * f (2 * n + 3 - 2 - j)
      = 2 * (R - (A + A ^ 2) - R') := by
    have h2 : (2 : ℤ[X]) * (∑ j ∈ range (2 * (n + 1)), C (δ j) * X * f j * f (2 * n + 3 - 2 - j)
        - 2 * (R - (A + A ^ 2) - R')) = 0 := by
      linear_combination -hR'
    rcases mul_eq_zero.mp h2 with h2 | h2
    · exact absurd h2 two_ne_zero
    · exact sub_eq_zero.mp h2
  have hbar := congrArg (Polynomial.map (Int.castRingHom (ZMod 2))) hsum2
  rw [Polynomial.map_mul, show Polynomial.map (Int.castRingHom (ZMod 2)) (2 : ℤ[X]) = 2 by simp,
    two_eq_zero_Z2X, zero_mul, Polynomial.map_sum] at hbar
  simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X] at hbar
  set w : ℕ → ZMod 2 := fun j => Int.castRingHom (ZMod 2) (δ j) with hw
  change ∑ j ∈ range (2 * (n + 1)), C (w j) * X * fbar j * fbar (2 * n + 3 - 2 - j) = 0 at hbar
  -- pair j with 2N - 1 - j
  rw [two_mul, Finset.sum_range_add] at hbar
  rw [← Finset.sum_range_reflect (fun j => C (w (n + 1 + j)) * X * fbar (n + 1 + j)
    * fbar (2 * n + 3 - 2 - (n + 1 + j))) (n + 1)] at hbar
  rw [← Finset.sum_add_distrib] at hbar
  have hpair : ∑ j ∈ range (n + 1),
      C (w j + w (2 * n + 1 - j)) * (fbar j * fbar (2 * (n + 1) - 1 - j)) = 0 := by
    have hX : (X : (ZMod 2)[X]) * ∑ j ∈ range (n + 1),
        C (w j + w (2 * n + 1 - j)) * (fbar j * fbar (2 * (n + 1) - 1 - j)) = 0 := by
      rw [← hbar, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      rw [show n + 1 + (n + 1 - 1 - j) = 2 * n + 1 - j by omega,
        show 2 * n + 3 - 2 - (2 * n + 1 - j) = j by omega,
        show 2 * n + 3 - 2 - j = 2 * n + 1 - j by omega,
        show 2 * (n + 1) - 1 - j = 2 * n + 1 - j by omega, C_add]
      ring
    rcases mul_eq_zero.mp hX with h0 | h0
    · exact absurd h0 X_ne_zero
    · exact h0
  have hw0 := indep (n + 1) (fun j => w j + w (2 * n + 1 - j)) hpair
  -- read off the signs: w j = 1 exactly where s differs from the reference sequence
  constructor
  · -- middle: j = n, partner 2n + 1 - n = n + 1
    have h0 := hw0 n (by omega)
    rw [show 2 * n + 1 - n = n + 1 by omega] at h0
    rcases hs n (by omega) with h1 | h1 <;> rcases hs (n + 1) (by omega) with h2 | h2 <;>
      simp [hw, δ, star, h1, h2] at h0 ⊢
  · intro i hi
    have h0 := hw0 i (by omega)
    have hi1 : i ≠ n + 1 := by omega
    have hi2 : 2 * n + 1 - i ≠ n + 1 := by omega
    rcases hs i (by omega) with h1 | h1 <;> rcases hs (2 * n + 1 - i) (by omega) with h2 | h2 <;>
      simp [hw, δ, star, hi1, hi2, h1, h2] at h0 ⊢
end Corless
