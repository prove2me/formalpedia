-- Prove2me | solution 1 for Function.bijective_of_fiber_card_bounds
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:04:45.855518+00:00
-- url     : https://prove2.me/submissions/6d6ea20c-3d4e-4c56-a187-5f19de0771a8

import Mathlib

set_option autoImplicit false

namespace Function

/-- Lower bounds on distinct fibres whose sum is the whole domain cardinality
    exhaust the codomain and are all equalities. -/
theorem _root_.solution
    {A B I : Type*} [Finite A] [Fintype I]
    (f : A → B) (hf : Surjective f) (p : I → B) (hp : Injective p)
    (w : I → ℕ) (hw : ∑ i, w i = Nat.card A)
    (hbound : ∀ i, w i ≤ Nat.card {a : A // f a = p i}) :
    Bijective p ∧ ∀ i, Nat.card {a : A // f a = p i} = w i := by
  classical
  let : Fintype A := Fintype.ofFinite A
  let : Finite B := Finite.of_surjective f hf
  let : Fintype B := Fintype.ofFinite B
  let c (b : B) := Fintype.card {a : A // f a = b}
  let s : Finset B := Finset.univ.image p
  have htotal : ∑ b : B, c b = Nat.card A := by
    rw [Nat.card_eq_fintype_card]
    calc
      _ = Fintype.card (Σ b : B, {a : A // f a = b}) := Fintype.card_sigma.symm
      _ = Fintype.card A := Fintype.card_congr (Equiv.sigmaFiberEquiv f)
  have hsum : ∑ b ∈ s, c b = ∑ i, c (p i) := by
    exact Finset.sum_image (fun _ _ _ _ h => hp h)
  have hle : ∑ i, c (p i) ≤ Nat.card A := by
    rw [← hsum, ← htotal]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ s)
  have hb (i : I) : w i ≤ c (p i) := by
    simpa only [c, Nat.card_eq_fintype_card] using hbound i
  have heq : ∑ i, c (p i) = Nat.card A :=
    le_antisymm hle (hw ▸ Finset.sum_le_sum (fun i _ => hb i))
  have hexact (i : I) : c (p i) = w i := by
    by_contra hn
    have hlt : ∑ j, w j < ∑ j, c (p j) :=
      Finset.sum_lt_sum (fun j _ => hb j)
        ⟨i, Finset.mem_univ i, lt_of_le_of_ne (hb i) (Ne.symm hn)⟩
    omega
  refine ⟨⟨hp, ?_⟩, fun i => ?_⟩
  · intro b
    by_contra hn
    have hnot : b ∉ s := by
      simpa only [s, Finset.mem_image, Finset.mem_univ, true_and] using hn
    obtain ⟨a, ha⟩ := hf b
    have hpos : 0 < c b := Fintype.card_pos_iff.mpr ⟨⟨a, ha⟩⟩
    have hle' : c b + ∑ x ∈ s, c x ≤ ∑ x : B, c x := by
      rw [← Finset.sum_insert hnot]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ (insert b s))
    rw [hsum, heq, htotal] at hle'
    omega
  · simpa only [c, Nat.card_eq_fintype_card] using hexact i

end Function
