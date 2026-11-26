-- Prove2me | solution 1 for Erdos287.opposite_parity_windows_count_short_even_runs
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T15:02:00.457301+00:00
-- url     : https://prove2.me/submissions/21240e8f-5be8-4977-8922-8eb32ea95b59

import Mathlib
import Theorems.Thm_Erdos287_opposite_parity_holes_enclose_even_run

open Finset

set_option autoImplicit false

/-- Many windows with both parities of holes force many distinct short even
runs. A given run can be counted at most once for each permitted offset. -/
theorem solution (H W : Finset ℕ) (d : ℕ) (hsep : ∀ n ∈ H, n + 1 ∉ H)
    (hW : ∀ t ∈ W, ∃ a ∈ H, ∃ b ∈ H, t ≤ a ∧ a < b ∧ b ≤ t + d ∧ a % 2 ≠ b % 2) :
    let runs := (H ×ˢ H).filter (fun xy => xy.1 + 3 ≤ xy.2 ∧ xy.2 - xy.1 ≤ d ∧
      Even (xy.2 - xy.1 - 1) ∧ ∀ n ∈ Finset.Ioo xy.1 xy.2, n ∉ H)
    W.card ≤ (d + 1) * runs.card := by
  classical
  let R := (H ×ˢ H).filter (fun xy => xy.1 + 3 ≤ xy.2 ∧ xy.2 - xy.1 ≤ d ∧
    Even (xy.2 - xy.1 - 1) ∧ ∀ n ∈ Ioo xy.1 xy.2, n ∉ H)
  change W.card ≤ (d + 1) * R.card
  have hchoose (t : ℕ) (ht : t ∈ W) : ∃ z ∈ R, t ≤ z.1 ∧ z.1 ≤ t + d := by
    obtain ⟨a, ha, b, hb, hta, hab, hbt, hp⟩ := hW t ht
    obtain ⟨x, hx, y, hy, hax, hyb, hd, he, hnone⟩ :=
      Erdos287.opposite_parity_holes_enclose_even_run H a b ha hb hab hp hsep
    have hi : ∀ n ∈ Ioo x y, n ∉ H :=
      fun n hn => hnone n (mem_Ioo.mp hn).1 (mem_Ioo.mp hn).2
    refine ⟨(x, y), mem_filter.mpr ⟨mem_product.mpr ⟨hx, hy⟩, hd, ?_, he, hi⟩,
      hta.trans hax, ?_⟩ <;> omega
  choose z hz hbound using hchoose
  let f (t : ↥W) := z t.val t.property
  have hmap : Set.MapsTo f (↑W.attach : Set ↥W) (↑R : Set (ℕ × ℕ)) :=
    fun t _ => hz t.val t.property
  have hfiber (v : ℕ × ℕ) : (W.attach.filter (fun t => f t = v)).card ≤ d + 1 := by
    let T := W.attach.filter (fun t => f t = v)
    have hmaps : Set.MapsTo (fun t : ↥W => t.val) (↑T : Set ↥W)
        (↑(Icc (v.1 - d) v.1) : Set ℕ) := by
      intro t ht
      have heq := (mem_filter.mp ht).2
      have htSpan := hbound t.val t.property
      change t.val ≤ (f t).1 ∧ (f t).1 ≤ t.val + d at htSpan
      rw [heq] at htSpan
      change t.val ∈ Icc (v.1 - d) v.1
      exact mem_Icc.mpr ⟨by omega, htSpan.1⟩
    have hinj : Set.InjOn (fun t : ↥W => t.val) (↑T : Set ↥W) :=
      fun _ _ _ _ h => Subtype.ext h
    calc
      _ ≤ (Icc (v.1 - d) v.1).card := card_le_card_of_injOn _ hmaps hinj
      _ ≤ _ := by rw [Nat.card_Icc]; omega
  calc
    W.card = W.attach.card := card_attach.symm
    _ = ∑ v ∈ R, (W.attach.filter (fun t => f t = v)).card := card_eq_sum_card_fiberwise hmap
    _ ≤ ∑ _v ∈ R, (d + 1) := sum_le_sum fun v _ => hfiber v
    _ = _ := by simp [mul_comm]

