-- Prove2me | solution 1 for Erdos3.green_tao
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T09:47:44.646337+00:00
-- url     : https://prove2.me/submissions/f2bd5c18-f8df-40c0-a951-cea5c636776e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Erdos142Basic
import Theorems.Thm_Erdos3_erdos_3

namespace OAIErdos3Cor

open Erdos142

/-- From the published Erdős Problem 3 statement: a set with non-summable reciprocals contains a
`k`-term progression with positive common difference, for every `k`. -/
theorem hasAP_of_not_summable {A : Set ℕ} (hA : ¬ Summable fun a : A ↦ 1 / (a : ℝ)) (k : ℕ) :
    ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A := by
  obtain ⟨m, ⟨S, hSA, a, d, hcard, hS⟩, hm⟩ :=
    ((Erdos3.erdos_3 A hA).and_eventually (Filter.eventually_ge_atTop (k + 2))).exists
  have hcard' : S.encard = (m : ℕ∞) := hcard
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · exfalso
      subst h0
      have hsub : S ⊆ {a} := by
        rw [hS]
        rintro _ ⟨n, _, rfl⟩
        simp
      have h1 : S.encard ≤ 1 := (Set.encard_le_encard hsub).trans_eq (Set.encard_singleton a)
      rw [hcard'] at h1
      have : m ≤ 1 := by exact_mod_cast h1
      omega
    · exact h0
  refine ⟨a, d, hd, fun i hi ↦ hSA ?_⟩
  rw [hS]
  exact ⟨i, by exact_mod_cast (show i < m by omega), by simp⟩

/-- The primes have non-summable reciprocals (Mathlib). -/
theorem not_summable_primes : ¬ Summable fun p : {p : ℕ | p.Prime} ↦ 1 / (p : ℝ) :=
  Nat.Primes.not_summable_one_div

theorem primes_hasAP (k : ℕ) : ∃ a d : ℕ, 0 < d ∧ ∀ i < k, (a + i * d).Prime :=
  hasAP_of_not_summable not_summable_primes k

/-- A progression `a, a + d, …, a + (k-1)d` with `d > 0` is a set of exactly `k` elements. -/
theorem image_isAPOfLengthWith (a d k : ℕ) (hd : 0 < d) :
    ENat.card ((fun n : ℕ ↦ a + n * d) '' Set.Iio k) = k ∧
      (fun n : ℕ ↦ a + n * d) '' Set.Iio k = {x | ∃ n : ℕ, ∃ (_ : (n : ℕ∞) < k), a + n • d = x} := by
  constructor
  · have hinj : Function.Injective (fun n : ℕ ↦ a + n * d) := by
      intro m n hmn
      have : m * d = n * d := by simpa using hmn
      exact Nat.eq_of_mul_eq_mul_right hd this
    rw [ENat.card_image_of_injective _ _ hinj]
    simp
  · ext x
    simp only [Set.mem_image, Set.mem_Iio, Set.mem_ofPred_eq, smul_eq_mul, Nat.cast_lt]
    constructor
    · rintro ⟨n, hn, rfl⟩; exact ⟨n, hn, rfl⟩
    · rintro ⟨n, hn, rfl⟩; exact ⟨n, hn, rfl⟩

end OAIErdos3Cor

namespace Erdos3
open Erdos142

theorem solution_aux : ∀ k : ℕ, ∃ S ⊆ {p : ℕ | p.Prime}, IsAPOfLength S k := by
  intro k
  obtain ⟨a, d, hd, h⟩ := OAIErdos3Cor.primes_hasAP k
  refine ⟨(fun n : ℕ ↦ a + n * d) '' Set.Iio k, ?_, a, d,
    OAIErdos3Cor.image_isAPOfLengthWith a d k hd⟩
  rintro _ ⟨n, hn, rfl⟩
  exact h n hn

end Erdos3

open Erdos142 in
theorem solution : ∀ k : ℕ, ∃ S ⊆ {p : ℕ | p.Prime}, IsAPOfLength S k :=
  Erdos3.solution_aux
