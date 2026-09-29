-- Prove2me | solution 1 for BlockCycleRotation.aggregate_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:51:44.078577+00:00
-- url     : https://prove2.me/submissions/beafcee7-56ce-4aa3-b021-afc8df0f4329

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_Theorem13
import Definitions.Def_BlockCycleRotation_TripleSum
import Theorems.Thm_BlockCycleRotation_middle_layer
import Theorems.Thm_BlockCycleRotation_outer_layer
import Mathlib

open Finset Real

namespace BlockCycleRotation

@[simp]
theorem remSum_zero (n : ℕ) : remSum n 0 = 0 := by
  rw [remSum]; simp

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

@[simp]
theorem cost_zero (n : ℕ) : cost n 0 = 0 := by
  rw [cost]; simp

@[simp]
theorem finalSeg_zero (n : ℕ) : finalSeg n 0 = n := by
  rw [finalSeg]; simp

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

@[simp] theorem K_nil : K [] = 1 := rfl

@[simp] theorem K_singleton (c : ℕ) : K [c] = c := rfl

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

theorem mem_coprimePairs {m a a' : ℕ} :
    (a, a') ∈ coprimePairs m ↔ (a ≤ m ∧ a' ≤ m) ∧ 1 ≤ a' ∧ a' < a ∧ Nat.gcd a a' = 1 := by
  simp [coprimePairs, Finset.mem_filter, Finset.mem_product, and_assoc]

end BlockCycleRotation

open BlockCycleRotation in
/-- A per-pair bound of size `W·(1 + log m)` aggregates to `Err n`.  This is the
middle and outer layer, applied to whichever of `G₂`, `G₃` is at hand. -/
theorem solution {n : ℕ} (hn : 0 < n) (F : ℕ → ℕ → ℕ → ℕ → ℝ)
    (hF : ∀ d ∈ n.divisors, ∀ p ∈ (coprimePairs (n / d)).filter
        (fun p => d * p.1 * (p.1 + p.2) ≤ n / d),
      |F (n / d) d p.1 p.2|
        ≤ (((d * p.1 : ℕ) : ℝ) + 2 * ((n / d : ℕ) : ℝ) / (p.1 : ℝ))
            * (1 + Real.log ((n / d : ℕ) : ℝ))) :
    |∑ d ∈ n.divisors, ∑ p ∈ (coprimePairs (n / d)).filter
        (fun p => d * p.1 * (p.1 + p.2) ≤ n / d), F (n / d) d p.1 p.2| ≤ Err n:= by
  classical
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hper : ∀ d ∈ n.divisors,
      |∑ p ∈ (coprimePairs (n / d)).filter (fun p => d * p.1 * (p.1 + p.2) ≤ n / d),
          F (n / d) d p.1 p.2|
        ≤ ((Nat.sqrt ((n / d - 1) / d) : ℝ) + 1)
            * (3 * ((n / d : ℕ) : ℝ) * (1 + Real.log ((n / d : ℕ) : ℝ))) := by
    intro d hd
    obtain ⟨hdn, -⟩ := Nat.mem_divisors.1 hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
    have hm0 : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdn) hd0
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum (hF d hd)) ?_
    have hsub : (coprimePairs (n / d)).filter (fun p => d * p.1 * (p.1 + p.2) ≤ n / d)
        ⊆ (coprimePairs (n / d)).filter (fun p => d * p.1 * p.1 < n / d) := by
      intro p hp
      rw [Finset.mem_filter] at hp ⊢
      obtain ⟨hpc, hpb⟩ := hp
      refine ⟨hpc, ?_⟩
      obtain ⟨a, a'⟩ := p
      obtain ⟨-, ha1, haa, -⟩ := mem_coprimePairs.1 hpc
      have ha : 0 < a := by omega
      have hpos : 0 < d * a * a' := Nat.mul_pos (Nat.mul_pos hd0 ha) (by omega)
      have hlt : d * a * a < d * a * (a + a') := by nlinarith
      exact lt_of_lt_of_le hlt hpb
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => by positivity) ?_
    exact middle_layer hm0 hd0
  refine le_trans (Finset.sum_le_sum hper) ?_
  rw [Err]
  exact outer_layer hn
