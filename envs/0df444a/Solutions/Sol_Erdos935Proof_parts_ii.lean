-- Prove2me | solution 1 for Erdos935Proof.parts_ii
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:45:00.185189+00:00
-- url     : https://prove2.me/submissions/ab1e21de-dc94-4d6e-94da-ec61c513cec3

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
theorem _root_.solution : ∀ ℓ : ℕ, 2 ≤ ℓ → ∀ C : ℝ, ∃ᶠ n : ℕ in atTop,
    C * (n : ℝ) ^ 2 < ((Erdos367.B 2 (∏ m ∈ Finset.Icc n (n + ℓ), m) : ℕ) : ℝ) := by
  intro ℓ hℓ C
  rw [frequently_atTop]
  intro N
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt C (by norm_num : (1 : ℝ) < 3)
  obtain ⟨x, y, h, hx, hy⟩ := exists_pell (N + K + 1)
  have hyx : y < x := lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) (by omega)
  obtain ⟨n, rfl⟩ : ∃ n, x = n + 1 := ⟨x - 1, by omega⟩
  have hn2 : 2 ^ 3 * y ^ 2 = n * (n + 2) := by nlinarith [h]
  have hsub : ({n, n + 1, n + 2} : Finset ℕ) ⊆ Finset.Icc n (n + ℓ) := by
    intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rw [Finset.mem_Icc]
    omega
  have hprod := Finset.prod_dvd_prod_of_subset _ _ (fun m : ℕ ↦ m) hsub
  rw [Finset.prod_insert (by simp), Finset.prod_insert (by simp), Finset.prod_singleton] at hprod
  have hdvd : 2 ^ 3 * y ^ 2 * 3 ^ (N + K + 2) ∣ ∏ m ∈ Finset.Icc n (n + ℓ), m := by
    refine dvd_trans ?_ hprod
    rw [hn2]
    calc n * (n + 2) * 3 ^ (N + K + 2) ∣ n * (n + 2) * (n + 1) := mul_dvd_mul_left _ hx
      _ = n * ((n + 1) * (n + 2)) := by ring
  have hP : ∏ m ∈ Finset.Icc n (n + ℓ), m ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun m hm ↦ by rw [Finset.mem_Icc] at hm; omega
  have hy0 : y ^ 2 ≠ 0 := pow_ne_zero _ (by omega)
  have hpow : ∀ p, (2 ^ 3 * y ^ 2 * 3 ^ (N + K + 2)).factorization p ≠ 1 :=
    factorization_mul_ne_one (mul_ne_zero (by norm_num) hy0) (by positivity)
      (factorization_mul_ne_one (by norm_num) hy0
        (factorization_pow_ne_one 2 (by norm_num)) (factorization_pow_ne_one y le_rfl))
      (factorization_pow_ne_one 3 (by omega))
  have hB := le_B_two hP hdvd hpow
  refine ⟨n, by omega, ?_⟩
  have hd : ((2 ^ 3 * y ^ 2 * 3 ^ (N + K + 2) : ℕ) : ℝ) = n * (n + 2) * 3 ^ (N + K + 2) := by
    rw [hn2]
    push_cast
    ring
  have hK' : C < 3 ^ (N + K + 2) := hK.trans_le (pow_le_pow_right₀ (by norm_num) (by omega))
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have h3 : (0 : ℝ) < 3 ^ (N + K + 2) := by positivity
  calc C * (n : ℝ) ^ 2 < 3 ^ (N + K + 2) * (n : ℝ) ^ 2 :=
        mul_lt_mul_of_pos_right hK' (pow_pos (by linarith) 2)
    _ ≤ n * (n + 2) * 3 ^ (N + K + 2) := by nlinarith
    _ = ((2 ^ 3 * y ^ 2 * 3 ^ (N + K + 2) : ℕ) : ℝ) := hd.symm
    _ ≤ _ := by exact_mod_cast hB
end Erdos935Proof
