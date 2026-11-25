-- Prove2me | solution 1 for ConjCoord.Proof.count_eq_cntL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:49:35.900458+00:00
-- url     : https://prove2.me/submissions/43a0958f-b0cd-4687-90de-f44be1f3cdf8

module
public import Definitions.Def_ConjCoord_Defs
public import Definitions.Def_ConjCoord_Compute
public import Theorems.Thm_ConjCoord_Proof_card_zfilter
public import Theorems.Thm_ConjCoord_Proof_sum_Icc_natAbs

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof
namespace ConjCoord.Proof
theorem _root_.solution (a b c n : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (P : ℤ → ℤ → Prop) [DecidableRel P] (Q : ℕ → ℕ → Bool)
    (hPQ : ∀ x y, P x y ↔ Q x.natAbs y.natAbs = true) :
    ((box3 n).filter fun v =>
        (a : ℤ) * v.1 ^ 2 + b * v.2.1 ^ 2 + c * v.2.2 ^ 2 = n ∧ P v.1 v.2.1).card =
      cntL a b c n Q := by
  set g : ℕ → ℕ → ℕ := fun i j =>
    if a * i ^ 2 + b * j ^ 2 ≤ n ∧ Q i j = true then zc c (n - a * i ^ 2 - b * j ^ 2) else 0
    with hg
  -- the inner count over `z`
  have inner : ∀ x y : ℤ,
      (∑ z ∈ Icc (-(n : ℤ)) n,
        if (a : ℤ) * x ^ 2 + b * y ^ 2 + c * z ^ 2 = n ∧ P x y then 1 else 0) =
        g x.natAbs y.natAbs := by
    intro x y
    rw [← card_filter]
    have hx : ((x.natAbs ^ 2 : ℕ) : ℤ) = x ^ 2 := by push_cast; exact sq_abs x
    have hy : ((y.natAbs ^ 2 : ℕ) : ℤ) = y ^ 2 := by push_cast; exact sq_abs y
    simp only [hg]
    by_cases hP : P x y
    · have hQ := (hPQ x y).mp hP
      have hfil : ((Icc (-(n : ℤ)) n).filter fun z =>
            (a : ℤ) * x ^ 2 + b * y ^ 2 + c * z ^ 2 = n ∧ P x y) =
          (Icc (-(n : ℤ)) n).filter fun z => (c : ℤ) * z ^ 2 = (n : ℤ) - a * x ^ 2 - b * y ^ 2 := by
        refine filter_congr fun z _ => ?_
        constructor
        · rintro ⟨h, -⟩; linarith
        · intro h; exact ⟨by linarith, hP⟩
      rw [hfil, card_zfilter c hc n _ (by nlinarith [sq_nonneg x, sq_nonneg y])]
      by_cases hle : a * x.natAbs ^ 2 + b * y.natAbs ^ 2 ≤ n
      · have h0 : (0 : ℤ) ≤ (n : ℤ) - a * x ^ 2 - b * y ^ 2 := by
          rw [← hx, ← hy]; have : ((a * x.natAbs ^ 2 + b * y.natAbs ^ 2 : ℕ) : ℤ) ≤ n := by
            exact_mod_cast hle
          push_cast at this ⊢; linarith
        rw [if_pos h0, if_pos ⟨hle, hQ⟩]
        congr 1
        rw [← hx, ← hy]
        have : ((n - a * x.natAbs ^ 2 - b * y.natAbs ^ 2 : ℕ) : ℤ) =
            (n : ℤ) - a * (x.natAbs ^ 2 : ℕ) - b * (y.natAbs ^ 2 : ℕ) := by
          push_cast [Nat.sub_sub, Nat.cast_sub hle]; ring
        omega
      · have h0 : ¬ (0 : ℤ) ≤ (n : ℤ) - a * x ^ 2 - b * y ^ 2 := by
          rw [← hx, ← hy]; have : ¬ ((a * x.natAbs ^ 2 + b * y.natAbs ^ 2 : ℕ) : ℤ) ≤ n := by
            exact_mod_cast hle
          push_cast at this ⊢; linarith
        rw [if_neg h0, if_neg (fun h => hle h.1)]
    · have hQ : ¬ Q x.natAbs y.natAbs = true := fun h => hP ((hPQ x y).mpr h)
      rw [if_neg (fun h => hQ h.2), card_eq_zero, filter_eq_empty_iff]
      exact fun z _ h => hP h.2
  rw [card_filter, box3, sum_product]
  simp_rw [sum_product]
  simp_rw [inner]
  rw [sum_Icc_natAbs n (fun i => ∑ y ∈ Icc (-(n : ℤ)) n, g i y.natAbs)]
  have hrow : ∀ i, ∑ y ∈ Icc (-(n : ℤ)) n, g i y.natAbs = ∑ j ∈ range (n + 1), wt j • g i j :=
    fun i => sum_Icc_natAbs n (g i)
  simp_rw [hrow]
  -- truncate the ranges
  have hvan : ∀ i j, Nat.sqrt n < i ∨ Nat.sqrt n < j → g i j = 0 := by
    intro i j hij
    simp only [hg]
    rw [if_neg]
    rintro ⟨hle, -⟩
    rcases hij with h | h
    · have := Nat.sqrt_lt'.mp h
      nlinarith [Nat.zero_le (b * j ^ 2)]
    · have := Nat.sqrt_lt'.mp h
      nlinarith [Nat.zero_le (a * i ^ 2)]
  have hsub : range (Nat.sqrt n + 1) ⊆ range (n + 1) := by
    intro k hk; simp only [mem_range] at hk ⊢; have := Nat.sqrt_le_self n; omega
  have hinner : ∀ i, ∑ j ∈ range (n + 1), wt j • g i j =
      ∑ j ∈ range (Nat.sqrt n + 1), wt j • g i j := by
    intro i
    refine (sum_subset hsub fun j _ hj => ?_).symm
    simp only [mem_range, not_lt] at hj
    rw [hvan i j (Or.inr (by omega)), smul_zero]
  simp_rw [hinner]
  rw [← sum_subset hsub fun i _ hi => ?_]
  · unfold cntL
    refine sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    simp only [hg, smul_eq_mul]
    split_ifs <;> ring
  · simp only [mem_range, not_lt] at hi
    rw [sum_eq_zero fun j _ => by rw [hvan i j (Or.inl (by omega)), smul_zero], smul_zero]
end ConjCoord.Proof
