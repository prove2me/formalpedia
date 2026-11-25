-- Prove2me | solution 1 for DegreeSequences.egReduce_sum_min
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:06:28.343721+00:00
-- url     : https://prove2.me/submissions/c2807784-5d87-427a-a607-8ef961f04434

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open DegreeSequences
namespace DegreeSequences
theorem _root_.solution {n : ℕ} (d : Fin n → ℕ) (t p : Fin n) (htp : t ≠ p) (ht : 1 ≤ d t)
    (hp : 1 ≤ d p) (k : ℕ) (F : Finset (Fin n)) :
    ∑ i ∈ F, min (d i) k = ∑ i ∈ F, min (egReduce d t p i) k +
      (if t ∈ F then (if d t ≤ k then 1 else 0) else 0) +
      (if p ∈ F then (if d p ≤ k then 1 else 0) else 0) := by
  have key : ∀ i, min (d i) k = min (egReduce d t p i) k +
      (if i = t then (if d t ≤ k then 1 else 0) else 0) +
      (if i = p then (if d p ≤ k then 1 else 0) else 0) := by
    intro i
    unfold egReduce
    rcases eq_or_ne i t with rfl | hit
    · simp only [ite_true, htp, ite_false]; split_ifs <;> omega
    rcases eq_or_ne i p with rfl | hip
    · simp only [ite_true, hit, ite_false]; split_ifs <;> omega
    simp [hit, hip]
  rw [Finset.sum_congr rfl fun i _ => key i, sum_add_distrib, sum_add_distrib, sum_ite_eq',
    sum_ite_eq']
end DegreeSequences
