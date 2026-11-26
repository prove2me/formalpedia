-- Prove2me | solution 1 for Erdos287.few_primes_can_have_admissible_used_layers
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T07:09:27.693132+00:00
-- url     : https://prove2.me/submissions/97b86878-0005-48a5-b6eb-416bacb50608

import Mathlib
import Theorems.Thm_Erdos287_exact_prime_power_in_reduced_denominator
import Theorems.Thm_Erdos287_few_exceptional_primes_for_cofactor_subsets

open Finset

set_option autoImplicit false

/-- Count the primes whose highest layer can use an admissible cofactor set
in some exact reciprocal sum of one. The denominator set may vary with the prime. -/
theorem solution (U P : Finset ℕ) (F : Finset (Finset ℕ)) (L Y K : ℕ)
    (hL : 0 < L) (hY : 2 ≤ Y) (hU : ∀ n ∈ U, 0 < n ∧ n ∣ L)
    (hF : ∀ T ∈ F, T ⊆ U ∧ T.Nonempty)
    (hP : ∀ p ∈ P, p.Prime ∧ Y ≤ p ∧ ¬ p ∣ L)
    (hbound : U.card * L < Y ^ (K + 1))
    (hconfig : ∀ p ∈ P, ∃ (D : Finset ℕ) (e : ℕ), 1 ≤ e ∧
      (∀ n ∈ D, 0 < n ∧ padicValNat p n ≤ e) ∧
      (∑ n ∈ D, (1 : ℚ) / n) = 1 ∧
      (D.filter (fun n => padicValNat p n = e)).image (fun n => n / p ^ e) ∈ F) :
    P.card ≤ F.card * K := by
  refine Erdos287.few_exceptional_primes_for_cofactor_subsets U P F L Y K hL hY hU hF
    (fun p hp => ⟨(hP p hp).1, (hP p hp).2.1⟩) hbound ?_
  intro p hp
  obtain ⟨D, e, he, hD, hsum, hfamily⟩ := hconfig p hp
  obtain ⟨hprime, _, hpL⟩ := hP p hp
  have : Fact p.Prime := ⟨hprime⟩
  let S := D.filter (fun n => padicValNat p n = e)
  let cof (n : ℕ) := n / p ^ e
  have hinj : Set.InjOn cof (↑S : Set ℕ) := by
    intro a ha b hb hab
    have hdvd (n : ℕ) (hn : n ∈ S) : p ^ e ∣ n := by
      obtain ⟨hnD, hnval⟩ := mem_filter.mp hn
      exact (padicValNat_dvd_iff_le (hD n hnD).1.ne').mpr hnval.ge
    calc
      a = cof a * p ^ e := (Nat.div_mul_cancel (hdvd a ha)).symm
      _ = cof b * p ^ e := by rw [hab]
      _ = b := Nat.div_mul_cancel (hdvd b hb)
  have hcof (n : ℕ) (hn : n ∈ D) (hv : padicValNat p n = e) : n / p ^ e ∣ L :=
    (hU _ ((hF _ hfamily).1 (mem_image_of_mem cof (mem_filter.mpr ⟨hn, hv⟩)))).2
  have hcriterion := Erdos287.exact_prime_power_in_reduced_denominator D (fun _ => 1) p e L
    hprime he hpL (fun n hn => (hD n hn).1) (fun n hn => (hD n hn).2) hcof
  refine ⟨S.image cof, hfamily, ?_⟩
  by_contra hnot
  rw [sum_image hinj] at hnot
  have hnot' : ¬ (p : ℤ) ∣ ∑ n ∈ S, ((L / cof n : ℕ) : ℤ) := by
    simpa only [← Nat.cast_sum, Int.natCast_dvd_natCast] using hnot
  have hval := hcriterion.mpr (by simpa only [one_mul] using hnot')
  have hpOne := padicValNat.eq_zero_of_not_dvd hprime.not_dvd_one
  simp only [Int.cast_one, hsum, Rat.den_one, hpOne] at hval
  omega

