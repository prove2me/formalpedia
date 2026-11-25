-- Prove2me | solution 1 for Erdos935Proof.mahler
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:45:02.974378+00:00
-- url     : https://prove2.me/submissions/bd8f4be3-c6c2-4f9f-ae74-c95ea7a6e529

module
public import Mathlib
public import Definitions.Def_Erdos935Palomar_Solution
public import Theorems.Thm_Erdos935Proof_factorization_mul_ne_one
public import Theorems.Thm_Erdos935Proof_factorization_pow_ne_one
public import Theorems.Thm_Erdos935Proof_le_B_two
public import Theorems.Thm_Erdos935Proof_exists_pell

set_option autoImplicit true
@[expose] public section
public section
open Filter
open Erdos935Proof
namespace Erdos935Proof
theorem _root_.solution : ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in atTop,
    (1 - ε) * (n : ℝ) ^ 2 <
      ((Erdos367.B 2 (∏ m ∈ Finset.Icc n (n + ℓ), m) : ℕ) : ℝ) := by
  intro ℓ hℓ ε hε
  rw [frequently_atTop]
  intro N
  obtain ⟨x, y, h, -, hy⟩ := exists_pell N
  have hyx : y < x := lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) (by omega)
  obtain ⟨n, hn⟩ : ∃ n, n = 8 * y ^ 2 := ⟨_, rfl⟩
  have hy2 : y ≤ y ^ 2 := by nlinarith
  have hsub : ({n, n + 1} : Finset ℕ) ⊆ Finset.Icc n (n + ℓ) := by
    intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rw [Finset.mem_Icc]
    omega
  have hprod := Finset.prod_dvd_prod_of_subset _ _ (fun m : ℕ ↦ m) hsub
  rw [Finset.prod_pair (by omega)] at hprod
  have hd : 2 ^ 3 * y ^ 2 * x ^ 2 = n * (n + 1) := by rw [h, hn]; ring
  have hP : ∏ m ∈ Finset.Icc n (n + ℓ), m ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun m hm ↦ by rw [Finset.mem_Icc] at hm; omega
  have hy0 : y ^ 2 ≠ 0 := pow_ne_zero _ (by omega)
  have hpow : ∀ p, (2 ^ 3 * y ^ 2 * x ^ 2).factorization p ≠ 1 :=
    factorization_mul_ne_one (mul_ne_zero (by norm_num) hy0) (pow_ne_zero _ (by omega))
      (factorization_mul_ne_one (by norm_num) hy0
        (factorization_pow_ne_one 2 (by norm_num)) (factorization_pow_ne_one y le_rfl))
      (factorization_pow_ne_one x le_rfl)
  have hdvd : 2 ^ 3 * y ^ 2 * x ^ 2 ∣ ∏ m ∈ Finset.Icc n (n + ℓ), m := by
    rw [hd]
    exact hprod
  have hB := le_B_two hP hdvd hpow
  rw [hd] at hB
  refine ⟨n, by omega, ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  calc (1 - ε) * (n : ℝ) ^ 2 < (n : ℝ) * (n + 1) := by
        nlinarith [mul_pos hε (pow_pos (show (0 : ℝ) < n by linarith) 2)]
    _ = ((n * (n + 1) : ℕ) : ℝ) := by push_cast; ring
    _ ≤ _ := by exact_mod_cast hB
end Erdos935Proof
