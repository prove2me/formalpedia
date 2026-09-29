-- Prove2me | solution 1 for BlockCycleRotation.sum_coprimePairs_filter
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:20:06.488162+00:00
-- url     : https://prove2.me/submissions/a3ca12a5-89a0-43a4-963a-d9b08f97affc

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_TripleSum
import Mathlib

open Real Finset

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
theorem e_zero : e 0 = 1 := by simp [e]

@[simp] theorem K_nil : K [] = 1 := rfl

@[simp] theorem K_singleton (c : ℕ) : K [c] = c := rfl

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

theorem mem_coprimePairs {m a a' : ℕ} :
    (a, a') ∈ coprimePairs m ↔ (a ≤ m ∧ a' ≤ m) ∧ 1 ≤ a' ∧ a' < a ∧ Nat.gcd a a' = 1 := by
  simp [coprimePairs, Finset.mem_filter, Finset.mem_product, and_assoc]

end BlockCycleRotation

open BlockCycleRotation in
/-- The pairs, decomposed by their first component. -/
theorem solution {M : Type*} [AddCommMonoid M] {m d : ℕ} (g : ℕ → ℕ → M) :
    ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * p.1 < m), g p.1 p.2
      = ∑ a ∈ (Finset.range (m + 1)).filter (fun a => d * a * a < m),
          ∑ a' ∈ (Finset.Ico 1 a).filter (fun x => Nat.gcd a x = 1), g a a':= by
  rw [Finset.sum_sigma']
  refine Finset.sum_bij' (i := fun p _ => (⟨p.1, p.2⟩ : (_ : ℕ) × ℕ))
    (j := fun q _ => (q.1, q.2)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, a'⟩ hp
    simp only [Finset.mem_filter] at hp
    obtain ⟨hpair, hda⟩ := hp
    obtain ⟨⟨han, ha'n⟩, ha1, ha2, hgcd⟩ := mem_coprimePairs.1 hpair
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    exact ⟨⟨by omega, hda⟩, ⟨ha1, ha2⟩, hgcd⟩
  · rintro ⟨a, a'⟩ hq
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hq
    obtain ⟨⟨ham, hda⟩, ⟨ha1, ha2⟩, hgcd⟩ := hq
    simp only [Finset.mem_filter]
    exact ⟨mem_coprimePairs.2 ⟨⟨by omega, by omega⟩, ha1, ha2, hgcd⟩, hda⟩
  · rintro ⟨a, a'⟩ _
    rfl
  · rintro ⟨a, a'⟩ _
    rfl
  · rintro ⟨a, a'⟩ _
    rfl
