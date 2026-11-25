-- Prove2me | solution 1 for ErdosGirth.exists_params
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:36:05.765093+00:00
-- url     : https://prove2.me/submissions/cd7a64e1-ff03-4437-bc90-41fa2f970946

module
public import Mathlib
public import Definitions.Def_GirthLib_ErdosGirthAux
public import Theorems.Thm_ErdosGirth_bound_cycles
public import Theorems.Thm_ErdosGirth_bound_indep
public import Theorems.Thm_ErdosGirth_exists_root_bracket

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosGirth
namespace ErdosGirth
theorem _root_.solution (g : ℕ) {ε : ℝ} (hε : 0 < ε) : ∃ N : ℕ, 0 < N ∧ ∀ n ≥ N, ∃ (p : ℝ) (t : ℕ),
    0 ≤ p ∧ p ≤ 1 ∧ (t : ℝ) ≤ ε * n ∧
    2 / ((2 * n : ℕ) : ℝ) * ∑ ℓ ∈ range (g + 1), (((2 * n : ℕ) : ℝ) * p) ^ ℓ
      + ((2 * n).choose t : ℝ) * (1 - p) ^ t.choose 2 < 1 := by
  set Q : ℕ := ⌈2 / ε⌉₊ + 4 * (g + 1) * (2 ^ (2 * g + 3)) ^ g
    + 6 * 2 ^ (2 * g + 1 + 3) * (2 * g + 1 + 3).factorial + 2 with hQ
  have hQ1 : 1 ≤ Q := by omega
  refine ⟨Q ^ (2 * g + 3), Nat.pow_pos hQ1, fun n hn => ?_⟩
  obtain ⟨q, hq1, hq2⟩ := exists_root_bracket (2 * g + 3) (2 * n) (by omega)
  have hqQ : Q ≤ q := by
    by_contra hlt
    have : (q + 1) ^ (2 * g + 3) ≤ Q ^ (2 * g + 3) := Nat.pow_le_pow_left (by omega) _
    omega
  have hqpos : 1 ≤ q := le_trans hQ1 hqQ
  have hq1R : (1 : ℝ) ≤ q := by exact_mod_cast hqpos
  have hqa : (1 : ℝ) ≤ (q : ℝ) ^ (2 * g + 1) := one_le_pow₀ hq1R
  refine ⟨1 / (q : ℝ) ^ (2 * g + 1), q ^ (2 * g + 1 + 1), by positivity,
    by rw [div_le_one (by positivity)]; exact hqa, ?_, ?_⟩
  · have hεq : 2 ≤ ε * q := by
      have h1 : 2 / ε ≤ (q : ℝ) := by
        calc 2 / ε ≤ (⌈2 / ε⌉₊ : ℝ) := Nat.le_ceil _
          _ ≤ q := by exact_mod_cast (by omega : ⌈2 / ε⌉₊ ≤ q)
      rw [div_le_iff₀ hε] at h1; linarith
    have hn2 : ((q : ℝ) ^ (2 * g + 3)) ≤ 2 * n := by exact_mod_cast hq1
    push_cast
    have h3 : (q : ℝ) ^ (2 * g + 3) = q * q ^ (2 * g + 1 + 1) := by ring
    nlinarith [pow_nonneg (Nat.cast_nonneg q : (0 : ℝ) ≤ q) (2 * g + 1 + 1)]
  · have hA := bound_cycles g q (by omega) ((2 * n : ℕ) : ℝ) (by exact_mod_cast hq1)
      (by exact_mod_cast hq2.le)
    have hm2 : ((2 * n : ℕ) : ℝ) ≤ ((q : ℝ) + 1) ^ (2 * g + 1 + 2) := by
      exact_mod_cast hq2.le
    have hB := bound_indep (2 * g + 1) q (q ^ (2 * g + 1 + 1)) (by omega) rfl
      ((2 * n : ℕ) : ℝ) (by positivity) hm2
    have hC : (((2 * n).choose (q ^ (2 * g + 1 + 1)) : ℕ) : ℝ)
        ≤ ((2 * n : ℕ) : ℝ) ^ (q ^ (2 * g + 1 + 1)) := by
      exact_mod_cast Nat.choose_le_pow _ _
    have hp1 : 0 ≤ 1 - 1 / (q : ℝ) ^ (2 * g + 1) := by
      rw [sub_nonneg, div_le_one (by positivity)]; exact hqa
    have := mul_le_mul_of_nonneg_right hC (pow_nonneg hp1 ((q ^ (2 * g + 1 + 1)).choose 2))
    linarith
end ErdosGirth
