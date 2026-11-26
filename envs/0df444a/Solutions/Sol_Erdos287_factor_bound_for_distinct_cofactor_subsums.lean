-- Prove2me | solution 1 for Erdos287.factor_bound_for_distinct_cofactor_subsums
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T16:51:14.407507+00:00
-- url     : https://prove2.me/submissions/3df5ad76-3fbb-47b0-a234-a8ff781d009e

import Mathlib

open Finset

set_option autoImplicit false

private def subsums {α : Type} (S : Finset α) (w : α → ℕ) : Finset ℕ :=
  S.powerset.image (fun T => ∑ x ∈ T, w x)

private theorem card_subsums_union_le {α : Type} [DecidableEq α]
    (S T : Finset α) (w : α → ℕ) :
    (subsums (S ∪ T) w).card ≤ (subsums S w).card * (subsums T w).card := by
  have hsubset : subsums (S ∪ T) w ⊆
      ((subsums S w) ×ˢ (subsums T w)).image (fun pair => pair.1 + pair.2) := by
    intro n hn
    obtain ⟨U, hU, rfl⟩ := mem_image.mp hn
    have hUsub := mem_powerset.mp hU
    have hleft : U ∩ S ⊆ S := inter_subset_right
    have hright : U \ S ⊆ T := by
      intro a ha
      obtain ⟨haU, haS⟩ := mem_sdiff.mp ha
      exact (mem_union.mp (hUsub haU)).resolve_left haS
    refine mem_image.mpr ⟨(∑ a ∈ U ∩ S, w a, ∑ a ∈ U \ S, w a), ?_, ?_⟩
    · exact mem_product.mpr ⟨mem_image.mpr ⟨_, mem_powerset.mpr hleft, rfl⟩,
        mem_image.mpr ⟨_, mem_powerset.mpr hright, rfl⟩⟩
    · change (∑ a ∈ U ∩ S, w a) + (∑ a ∈ U \ S, w a) = ∑ a ∈ U, w a
      exact sum_inter_add_sum_sdiff U S w
  exact (card_le_card hsubset).trans (card_image_le.trans (by rw [card_product]))

private theorem card_subsums_biUnion_le {ι α : Type} [DecidableEq α]
    (I : Finset ι) (A : ι → Finset α) (w : α → ℕ) :
    (subsums (I.biUnion A) w).card ≤ ∏ j ∈ I, (subsums (A j) w).card := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [subsums]
  | insert j I hj ih =>
    rw [biUnion_insert, prod_insert hj]
    exact (card_subsums_union_le (A j) (I.biUnion A) w).trans
      (Nat.mul_le_mul_left _ ih)

/-- A core whose weights are multiples of `d` and total at most `d * K`
contributes at most `K + 1` distinct sums. Each other block contributes only
its own number of distinct sums to the product bound. -/
theorem solution {ι α : Type} [DecidableEq α] (I : Finset ι) (core : Finset α)
    (A : ι → Finset α) (w : α → ℕ) (d K : ℕ) (hd : 0 < d)
    (hdiv : ∀ a ∈ core, d ∣ w a) (hcap : (∑ a ∈ core, w a) ≤ d * K) :
    let sums := fun S : Finset α => S.powerset.image (fun T => ∑ a ∈ T, w a)
    (sums (core ∪ I.biUnion A)).card ≤ (K + 1) * ∏ j ∈ I, (sums (A j)).card := by
  change (subsums (core ∪ I.biUnion A) w).card ≤
    (K + 1) * ∏ j ∈ I, (subsums (A j) w).card
  have hvalue (n : ℕ) (hn : n ∈ subsums core w) : d ∣ n ∧ n ≤ d * K := by
    obtain ⟨T, hT, rfl⟩ := mem_image.mp hn
    have hsub := mem_powerset.mp hT
    exact ⟨dvd_sum fun a ha => hdiv a (hsub ha),
      (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)).trans hcap⟩
  have hmap : Set.MapsTo (fun n : ℕ => n / d) (↑(subsums core w) : Set ℕ)
      (↑(range (K + 1)) : Set ℕ) := by
    intro n hn
    have hle : n / d ≤ (d * K) / d := Nat.div_le_div_right (hvalue n hn).2
    rw [Nat.mul_div_cancel_left _ hd] at hle
    exact mem_range.mpr (Nat.lt_succ_of_le hle)
  have hinj : Set.InjOn (fun n : ℕ => n / d) (↑(subsums core w) : Set ℕ) := by
    intro x hx y hy he
    calc
      x = (x / d) * d := (Nat.div_mul_cancel (hvalue x hx).1).symm
      _ = (y / d) * d := congrArg (fun z => z * d) he
      _ = y := Nat.div_mul_cancel (hvalue y hy).1
  have hcore : (subsums core w).card ≤ K + 1 := by
    simpa only [card_range] using card_le_card_of_injOn (fun n : ℕ => n / d) hmap hinj
  exact (card_subsums_union_le core (I.biUnion A) w).trans <|
    Nat.mul_le_mul hcore (card_subsums_biUnion_le I A w)

