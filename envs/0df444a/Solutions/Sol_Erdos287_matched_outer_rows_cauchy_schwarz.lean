-- Prove2me | solution 1 for Erdos287.matched_outer_rows_cauchy_schwarz
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T18:51:29.010957+00:00
-- url     : https://prove2.me/submissions/43ab57be-402b-4572-82ea-32f38a753688

import Mathlib

open Finset

set_option autoImplicit false

/-- Cauchy–Schwarz on the matched outer rows of the dispersion sum.
Each row has its own base modulus, and its lift factor is `T`. -/
theorem solution {ι : Type*} (rows : Finset ι) (modulus residue : ι → ℕ) (T : ℕ)
    (hmodulus : ∀ i ∈ rows, 0 < modulus i) (value : ι → ℕ → ℝ) :
    let matched (i : ι) := (Finset.range (modulus i * T)).filter (fun u => u ≡ residue i [MOD modulus i])
    (∑ i ∈ rows, ∑ u ∈ matched i, value i u) ^ 2 ≤
      (rows.card : ℝ) * T * (∑ i ∈ rows, ∑ u ∈ Finset.range (modulus i * T), value i u ^ 2) := by
  classical
  dsimp only
  let matched (i : ι) := (range (modulus i * T)).filter (fun u => u ≡ residue i [MOD modulus i])
  let indices := rows.sigma matched
  change (∑ i ∈ rows, ∑ u ∈ matched i, value i u) ^ 2 ≤ _
  have hcount (i : ι) (hi : i ∈ rows) : (matched i).card = T := by
    dsimp only [matched]
    rw [← Nat.count_eq_card_filter_range, Nat.count_modEq_card _ (hmodulus i hi)]
    simp [(hmodulus i hi).ne']
  have hcard : indices.card = rows.card * T := by
    rw [card_sigma]
    calc
      ∑ i ∈ rows, (matched i).card = ∑ _i ∈ rows, T := sum_congr rfl hcount
      _ = rows.card * T := by simp
  have hcauchy : (∑ z ∈ indices, value z.1 z.2) ^ 2 ≤
      (indices.card : ℝ) * ∑ z ∈ indices, value z.1 z.2 ^ 2 := by
    simpa using (sum_mul_sq_le_sq_mul_sq indices (fun _ => (1 : ℝ)) (fun z => value z.1 z.2))
  have hmatched : (∑ i ∈ rows, ∑ u ∈ matched i, value i u ^ 2) ≤
      ∑ i ∈ rows, ∑ u ∈ range (modulus i * T), value i u ^ 2 := by
    apply sum_le_sum
    intro i _
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun u _ _ => sq_nonneg _)
  have hcast : (indices.card : ℝ) = (rows.card : ℝ) * T := by exact_mod_cast hcard
  calc
    (∑ i ∈ rows, ∑ u ∈ matched i, value i u) ^ 2 ≤
        ((rows.card : ℝ) * T) * (∑ i ∈ rows, ∑ u ∈ matched i, value i u ^ 2) := by
      rw [← hcast]
      simpa only [indices, sum_sigma] using hcauchy
    _ ≤ _ := mul_le_mul_of_nonneg_left hmatched (by positivity)

