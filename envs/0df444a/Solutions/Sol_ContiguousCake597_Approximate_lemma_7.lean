-- Prove2me | solution 1 for ContiguousCake597.Approximate.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-21T16:18:10.767116+00:00
-- url     : https://prove2.me/submissions/6e8fa5e0-a2f2-4a77-80aa-40e2fdef27cc

import Definitions.Def_ContiguousCake597_Approximate_Analysis

set_option autoImplicit false

namespace ContiguousCake597.Approximate.PriceRangeProof

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem positive_variation_bound (p : α → α) (sigma : Equiv.Perm α)
    (e : ℝ) (q : α → ℝ)
    (hq : ∀ i, max (q i) (q (p i)) - e ≤ q (sigma i)) :
    (∑ i, max (q (p i) - q i) 0) ≤ (Fintype.card α : ℝ) * e := by
  have hlocal (i : α) : max (q (p i) - q i) 0 ≤ q (sigma i) - q i + e := by
    apply max_le
    · have hi := le_max_right (q i) (q (p i))
      linarith [hq i]
    · have hi := le_max_left (q i) (q (p i))
      linarith [hq i]
  calc
    (∑ i, max (q (p i) - q i) 0) ≤ ∑ i, (q (sigma i) - q i + e) :=
      Finset.sum_le_sum (fun i _ => hlocal i)
    _ = (Fintype.card α : ℝ) * e := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Equiv.sum_comp]
      simp

theorem variation_controls_reachable (p : α → α) (q : α → ℝ) (i j : α)
    (hreach : ∃ k : ℕ, (p^[k]) i = j) :
    q j - q i ≤ ∑ x, max (q (p x) - q x) 0 := by
  classical
  let k := Nat.find hreach
  have hk : (p^[k]) i = j := Nat.find_spec hreach
  have hminimal {t : ℕ} (ht : (p^[t]) i = j) : k ≤ t := Nat.find_min' hreach ht
  have hdistinct (a b : ℕ) (hb : b < k) (hab : a < b) :
      (p^[a]) i ≠ (p^[b]) i := by
    intro heq
    have htarget : (p^[k - b + a]) i = j := by
      rw [Function.iterate_add_apply, heq, ← Function.iterate_add_apply,
        Nat.sub_add_cancel hb.le]
      exact hk
    have := hminimal htarget
    omega
  have hinj : Set.InjOn (fun t => (p^[t]) i) (↑(Finset.range k) : Set ℕ) := by
    intro a ha b hb heq
    have hak := Finset.mem_range.mp ha
    have hbk := Finset.mem_range.mp hb
    rcases lt_trichotomy a b with hab | hab | hab
    · exact (hdistinct a b hbk hab heq).elim
    · exact hab
    · exact (hdistinct b a hak hab heq.symm).elim
  calc
    q j - q i = ∑ t ∈ Finset.range k,
        (q ((p^[t + 1]) i) - q ((p^[t]) i)) := by
      rw [Finset.sum_range_sub (fun t => q ((p^[t]) i)) k, hk]
      rfl
    _ ≤ ∑ t ∈ Finset.range k, max (q (p ((p^[t]) i)) - q ((p^[t]) i)) 0 := by
      apply Finset.sum_le_sum
      intro t _
      rw [Function.iterate_succ_apply']
      exact le_max_left _ _
    _ = ∑ x ∈ (Finset.range k).image (fun t => (p^[t]) i),
        max (q (p x) - q x) 0 :=
      (Finset.sum_image (f := fun x => max (q (p x) - q x) 0) hinj).symm
    _ ≤ ∑ x, max (q (p x) - q x) 0 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro x _ _
      exact le_max_right _ _

end ContiguousCake597.Approximate.PriceRangeProof

namespace ContiguousCake597.Approximate

theorem lemma_7_proof (n : ℕ) (hn : 1 ≤ n) (p sigma : Equiv.Perm (Fin n))
    (hp : SingleCycle p) (e : ℝ) (he : 0 ≤ e) (q : Fin n → ℝ)
    (hq : ∀ i, max (q i) (q (p i)) - e ≤ q (sigma i)) :
    ∀ i j : Fin n, q j - q i ≤ (n : ℝ) * e := by
  intro i j
  exact (PriceRangeProof.variation_controls_reachable p q i j (hp i j)).trans
    (by simpa using PriceRangeProof.positive_variation_bound p sigma e q hq)

end ContiguousCake597.Approximate



open ContiguousCake597.Approximate

theorem solution (n : ℕ) (hn : 1 ≤ n) (p sigma : Equiv.Perm (Fin n))
    (hp : SingleCycle p) (e : ℝ) (he : 0 ≤ e) (q : Fin n → ℝ)
    (hq : ∀ i, max (q i) (q (p i)) - e ≤ q (sigma i)) :
    ∀ i j : Fin n, q j - q i ≤ (n : ℝ) * e := by
  exact ContiguousCake597.Approximate.lemma_7_proof n hn p sigma hp e he q hq

#print axioms solution
