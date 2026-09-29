-- Prove2me | solution 1 for EulerGammaResearch.variable_order_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-14T06:42:49.022429+00:00
-- url     : https://prove2.me/submissions/49e7d40d-812a-4bd2-8c7b-ab3875df75c2

import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

open scoped BigOperators

private lemma harmonic_nonneg' (n : ℕ) : 0 ≤ harmonic n := by
  unfold harmonic
  exact Finset.sum_nonneg (by intro i hi; positivity)

private lemma harmonic_mono' {k n : ℕ} (h : k ≤ n) : harmonic k ≤ harmonic n := by
  unfold harmonic
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h)
    (by intro i hi hni; positivity)

private lemma harmonic_tail_half (n k : ℕ) (hn : 0 < n) (hk : k ≤ n) :
    (1 / 2 : ℚ) ≤ harmonic (n+k) - harmonic k := by
  have hnq : (0 : ℚ) < n := by exact_mod_cast hn
  have heq : harmonic (n+k) - harmonic k =
      ∑ i ∈ Finset.range n, ((k+i+1 : ℕ) : ℚ)⁻¹ := by
    rw [Nat.add_comm n k, harmonic, Finset.sum_range_add]
    simp [harmonic, Nat.add_assoc]
  rw [heq]
  calc
    (1 / 2 : ℚ) = ∑ i ∈ Finset.range n, (2 * (n : ℚ))⁻¹ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i < n := Finset.mem_range.mp hi
      have hbound : (k+i+1 : ℕ) ≤ 2*n := by omega
      apply inv_anti₀ (by positivity)
      exact_mod_cast hbound

/-- Derived during the variable-order experiment. This excludes excessive order,
not irrationality of Euler's constant. No asymptotic hypothesis is used. -/
theorem solution (n p : ℕ) (hn : 0 < n) :
    let c : ℕ → ℚ := fun k => (n.choose k : ℚ)^2 * ((n+k).choose k : ℚ)^p /
      (k.factorial : ℚ);
    -(∑ k ∈ Finset.range (n+1), c k *
      ((p : ℚ)*harmonic (n+k) + 2*harmonic (n-k) - ((p : ℚ)+3)*harmonic k))
      / (∑ k ∈ Finset.range (n+1), c k) ≤ 3*harmonic n - (p : ℚ)/2 := by
  dsimp only
  let c : ℕ → ℚ := fun k => (n.choose k : ℚ)^2 * ((n+k).choose k : ℚ)^p /
    (k.factorial : ℚ)
  change -(∑ k ∈ Finset.range (n+1), c k * _) / (∑ k ∈ Finset.range (n+1), c k) ≤ _
  have hQ : 0 < ∑ k ∈ Finset.range (n+1), c k := by
    apply Finset.sum_pos' (by intro k hk; dsimp [c]; positivity)
    refine ⟨0, by simp, ?_⟩
    norm_num [c]
  apply (div_le_iff₀ hQ).mpr
  rw [← Finset.sum_neg_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have ht := harmonic_tail_half n k hn hkn
  have hm := harmonic_mono' hkn
  have hz := harmonic_nonneg' (n-k)
  have hp : (0 : ℚ) ≤ p := by positivity
  have hprod := mul_nonneg hp (sub_nonneg.mpr ht)
  have hbracket : (p : ℚ)/2 - 3*harmonic n ≤
      (p : ℚ)*harmonic (n+k) + 2*harmonic (n-k) - ((p : ℚ)+3)*harmonic k := by
    nlinarith
  have hc : 0 ≤ c k := by dsimp [c]; positivity
  nlinarith [mul_nonneg hc (sub_nonneg.mpr hbracket)]

#print axioms solution
