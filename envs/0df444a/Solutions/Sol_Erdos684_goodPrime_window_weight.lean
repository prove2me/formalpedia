-- Prove2me | solution 1 for Erdos684.goodPrime_window_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:56:15.28363+00:00
-- url     : https://prove2.me/submissions/ca161cea-d66b-49fa-ac98-9b7a58c9a35b

module
public import Definitions.Def_Erdos684_Finite
public import Definitions.Def_Erdos684_BadPrimes
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Definitions.Def_Erdos684_Averaging
public import Theorems.Thm_Erdos684_primeWeight_nonneg
public import Theorems.Thm_Erdos684_one_le_factorization_choose_of_mod_lt


set_option autoImplicit false
@[expose] public section
public section
open Finset Real
open Erdos684
namespace Erdos684
theorem _root_.solution {n X A p : ℕ} (hX : 2 * X ≤ n)
    (hp : p ∈ goodPrimes n X A) :
    (A : ℝ) * log p ≤ ∑ k ∈ Finset.Icc 1 (2 * X), primeWeight n k p := by
  classical
  obtain ⟨hpX, hgap⟩ := Finset.mem_filter.mp hp
  have hprime := Nat.prime_of_mem_primesLE hpX
  have hp_le := Nat.le_of_mem_primesLE hpX
  have hr := Nat.mod_lt n hprime.pos
  let g : ℕ → ℕ := fun i => p + n % p + i
  let T := (Finset.Icc 1 A).image g
  have hinj : Function.Injective g := by
    intro i j hij
    dsimp [g] at hij
    omega
  have hT : T ⊆ Finset.Icc 1 (2 * X) := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨hi1, hiA⟩ := Finset.mem_Icc.mp hi
    dsimp [g]
    apply Finset.mem_Icc.mpr
    omega
  have hbound : ∀ k ∈ T, log (p : ℝ) ≤ primeWeight n k p := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨hi1, hiA⟩ := Finset.mem_Icc.mp hi
    have hrem : n % p + i < p := by omega
    have hmod : n % p < g i % p := by
      dsimp [g]
      rw [Nat.add_assoc, Nat.add_mod_left, Nat.mod_eq_of_lt hrem]
      omega
    have hkn : g i ≤ n := (Finset.mem_Icc.mp (hT (Finset.mem_image.mpr ⟨i, by simp [hi1, hiA], rfl⟩))).2.trans hX
    have hfac := one_le_factorization_choose_of_mod_lt hprime hkn hmod
    have hpk : p ≤ g i := by dsimp [g]; omega
    rw [primeWeight, if_pos hpk]
    have hfacr : (1 : ℝ) ≤ (n.choose (g i)).factorization p := by exact_mod_cast hfac
    have hlp : 0 ≤ log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hprime.one_lt.le)
    nlinarith [hlp]
  calc
    (A : ℝ) * log p = ∑ k ∈ T, log (p : ℝ) := by
      simp [T, Finset.card_image_of_injective _ hinj]
    _ ≤ ∑ k ∈ T, primeWeight n k p := Finset.sum_le_sum hbound
    _ ≤ ∑ k ∈ Finset.Icc 1 (2 * X), primeWeight n k p :=
      Finset.sum_le_sum_of_subset_of_nonneg hT fun k _ _ => primeWeight_nonneg n k p hprime
end Erdos684
