-- Prove2me | solution 1 for Erdos287.fixed_layer_square_neighbors_at_most_two_progressions
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T14:24:02.827501+00:00
-- url     : https://prove2.me/submissions/b72f10b5-f23a-4590-af49-c63e99bac322

import Mathlib

open Finset

set_option autoImplicit false

/-- At a fixed prime layer, a prescribed multiple of a square can block
cofactors through at most two residue classes for the square root. -/
theorem solution (p b U : ℕ) (e : ℤ) (Q : Finset ℕ) (hp : p.Prime) (hb : ¬ p ∣ b)
    (hQ : ∀ q ∈ Q, q ≤ U) :
    (Q.filter (fun q : ℕ => (p : ℤ) ∣ (b : ℤ) * (q : ℤ) ^ 2 + e)).card ≤
      2 * (U / p + 1) := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  let F := Q.filter (fun q : ℕ => (p : ℤ) ∣ (b : ℤ) * (q : ℤ) ^ 2 + e)
  change F.card ≤ _
  by_cases hF : F.Nonempty
  · obtain ⟨r, hr⟩ := hF
    let V : Finset (ZMod p) := {(r : ZMod p), -(r : ZMod p)}
    have hroot (q : ℕ) (hq : q ∈ F) : (b : ZMod p) * (q : ZMod p) ^ 2 + (e : ZMod p) = 0 := by
      obtain ⟨j, hj⟩ := (mem_filter.mp hq).2
      simpa using congrArg (fun x : ℤ => (x : ZMod p)) hj
    have hbz : (b : ZMod p) ≠ 0 := fun hz => hb ((ZMod.natCast_eq_zero_iff b p).mp hz)
    have hmaps : Set.MapsTo (fun q : ℕ => (q : ZMod p)) (↑F : Set ℕ) (↑V : Set (ZMod p)) := by
      intro q hq
      have heq : (b : ZMod p) * (q : ZMod p) ^ 2 = (b : ZMod p) * (r : ZMod p) ^ 2 := by
        linear_combination hroot q hq - hroot r hr
      have hsquare := mul_left_cancel₀ hbz heq
      have hzero : ((q : ZMod p) - (r : ZMod p)) * ((q : ZMod p) + (r : ZMod p)) = 0 := by
        linear_combination hsquare
      rcases mul_eq_zero.mp hzero with h | h
      · exact mem_insert.mpr (Or.inl (sub_eq_zero.mp h))
      · exact mem_insert.mpr (Or.inr (mem_singleton.mpr (add_eq_zero_iff_eq_neg.mp h)))
    have hfiber (z : ZMod p) : (F.filter (fun q : ℕ => (q : ZMod p) = z)).card ≤ U / p + 1 := by
      let R := F.filter (fun q : ℕ => (q : ZMod p) = z)
      have hmap : Set.MapsTo (fun q : ℕ => q / p) (↑R : Set ℕ) (↑(range (U / p + 1)) : Set ℕ) := by
        intro q hq
        have hqU := hQ q (mem_filter.mp (mem_filter.mp hq).1).1
        exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hqU))
      have hi : Set.InjOn (fun q : ℕ => q / p) (↑R : Set ℕ) := by
        intro q hq t ht he
        change q / p = t / p at he
        have hm : q % p = t % p := (ZMod.natCast_eq_natCast_iff' q t p).mp
          ((mem_filter.mp hq).2.trans (mem_filter.mp ht).2.symm)
        calc
          q = q % p + p * (q / p) := (Nat.mod_add_div q p).symm
          _ = t % p + p * (t / p) := by rw [hm, he]
          _ = t := Nat.mod_add_div t p
      simpa using card_le_card_of_injOn (fun q : ℕ => q / p) hmap hi
    have hV : V.card ≤ 2 := (card_insert_le _ _).trans_eq (by simp)
    calc
      F.card = ∑ z ∈ V, (F.filter (fun q : ℕ => (q : ZMod p) = z)).card :=
        card_eq_sum_card_fiberwise hmaps
      _ ≤ ∑ _ ∈ V, (U / p + 1) := sum_le_sum fun z _ => hfiber z
      _ = V.card * (U / p + 1) := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ hV
  · simp [not_nonempty_iff_eq_empty.mp hF]

