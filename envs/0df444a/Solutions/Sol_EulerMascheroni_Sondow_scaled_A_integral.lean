-- Prove2me | solution 1 for EulerMascheroni.Sondow.scaled_A_integral
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-14T09:09:06.801982+00:00
-- url     : https://prove2.me/submissions/6eeb2956-95c1-4ef3-8c1a-f31054b23746

import Definitions.Def_eulerMascheroni_sondow
import Mathlib.Tactic

open Finset EulerMascheroni.Sondow

private lemma harmonic_integral (m N : ℕ) (hm : m ≤ N) :
    ∃ z : ℤ, (d N : ℚ) * harmonic m = z := by
  induction m with
  | zero => exact ⟨0, by simp⟩
  | succ m ih =>
    obtain ⟨z, hz⟩ := ih (by omega)
    have hd : m + 1 ∣ d N := Finset.dvd_lcm (f := id) (by simp; omega)
    obtain ⟨k, hk⟩ := hd
    refine ⟨z + k, ?_⟩
    rw [harmonic_succ, mul_add, hz]
    have he : (d N : ℚ) * (↑(m + 1))⁻¹ = (k : ℚ) := by
      rw [hk, Nat.cast_mul]
      field_simp
    simpa using congrArg (fun t : ℚ => (z : ℚ) + t) he

theorem solution (n : ℕ) : ∃ z : ℤ, (d (2*n) : ℝ) * (A n : ℝ) = z := by
  have h : ∀ i ∈ range (n+1), ∃ z : ℤ,
      (d (2*n) : ℚ) * ((n.choose i : ℚ)^2 * harmonic (n+i)) = z := by
    intro i hi
    obtain ⟨z, hz⟩ := harmonic_integral (n+i) (2*n) (by simp only [mem_range] at hi; omega)
    refine ⟨(n.choose i : ℤ)^2 * z, ?_⟩
    push_cast
    rw [← hz]
    ring
  choose z hz using fun i : {i // i ∈ range (n+1)} => h i.val i.property
  refine ⟨∑ i : {i // i ∈ range (n+1)}, z i, ?_⟩
  have hq : (d (2*n) : ℚ) * A n =
      ((∑ i : {i // i ∈ range (n+1)}, z i : ℤ) : ℚ) := by
    unfold A
    rw [mul_sum, ← sum_coe_sort]
    push_cast
    exact Fintype.sum_congr _ _ hz
  exact_mod_cast hq

#print axioms solution
