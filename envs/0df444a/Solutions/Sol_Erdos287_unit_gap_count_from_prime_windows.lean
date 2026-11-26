-- Prove2me | solution 1 for Erdos287.unit_gap_count_from_prime_windows
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T05:16:57.389298+00:00
-- url     : https://prove2.me/submissions/a61f5535-1c2f-48ba-89f1-ff9776fddb86

import Mathlib
import Theorems.Thm_Erdos287_no_denominator_multiple_of_large_prime_above_third

open Finset

set_option autoImplicit false

private theorem neighbors_of_omission
    {k : ℕ} (hk : 2 ≤ k) {f : ℕ → ℕ}
    (hgap : ∀ i, i + 1 < k → f (i + 1) - f i ≤ 2)
    {x : ℕ} (hx₀ : f 0 < x) (hx₁ : x < f (k - 1))
    (hmiss : ∀ i, i < k → f i ≠ x) :
    ∃ i, i + 1 < k ∧ f i + 1 = x ∧ f (i + 1) = x + 1 := by
  classical
  let S := (range k).filter (fun j => f j < x)
  have hs : S.Nonempty := ⟨0, mem_filter.mpr ⟨mem_range.mpr (by omega), hx₀⟩⟩
  let i := S.max' hs
  have hi := mem_filter.mp (S.max'_mem hs)
  change i ∈ range k ∧ f i < x at hi
  have hik := mem_range.mp hi.1
  have hil : i + 1 < k := by
    by_contra! h
    have he : i = k - 1 := by omega
    rw [he] at hi
    exact (not_lt_of_gt hx₁) hi.2
  have hupper : x < f (i + 1) := by
    have hn := hmiss (i + 1) hil
    by_contra! h
    have hp : i + 1 ∈ S := mem_filter.mpr ⟨mem_range.mpr hil, by omega⟩
    have hmax := S.le_max' (i + 1) hp
    change i + 1 ≤ i at hmax
    omega
  have hg := hgap i hil
  exact ⟨i, hil, by omega, by omega⟩

private theorem interval_contains_unit_gap
    {k : ℕ} (hk : 2 ≤ k) {f : ℕ → ℕ}
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hgap : ∀ i, i + 1 < k → f (i + 1) - f i ≤ 2)
    {x y : ℕ} (hx₀ : f 0 < x) (hy₁ : y < f (k - 1))
    (hspace : x + 3 ≤ y) (hpar : x % 2 ≠ y % 2)
    (hx : ∀ i, i < k → f i ≠ x) (hy : ∀ i, i < k → f i ≠ y) :
    ∃ i, i + 1 < k ∧ f (i + 1) - f i = 1 ∧ x < f i ∧ f (i + 1) < y := by
  obtain ⟨a, ha, _, haf⟩ := neighbors_of_omission hk hgap hx₀ (by omega) hx
  obtain ⟨b, hb, hbf, _⟩ := neighbors_of_omission hk hgap (by omega) hy₁ hy
  have hab : a + 1 ≤ b := by
    by_contra! h
    have hlt := hmono b (a + 1) h ha
    omega
  by_contra! h
  have hc : ∀ j, a + 1 ≤ j → j ≤ b → f j % 2 = f (a + 1) % 2 := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => simp
    | succ j hj ih =>
      intro hjb
      have hjk : j + 1 < k := by omega
      have hjx : x < f j := by
        rcases eq_or_lt_of_le hj with he | hl
        · rw [← he, haf]; omega
        · have hm := hmono (a + 1) j hl (by omega)
          omega
      have hjy : f (j + 1) < y := by
        rcases eq_or_lt_of_le hjb with he | hl
        · rw [he]; omega
        · have hm := hmono (j + 1) b hl (by omega)
          omega
      have hne : f (j + 1) - f j ≠ 1 := fun he => by
        have hn := h j hjk he hjx
        omega
      have hpos := hmono j (j + 1) (by omega) hjk
      have hsmall := hgap j hjk
      have hp := ih (by omega)
      omega
  have hsame := hc b hab le_rfl
  omega

/-- Prime and doubled-prime omissions in sliding windows force many unit gaps. -/
theorem solution (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hgap : ∀ i, i + 1 < k → f (i + 1) - f i ≤ 2)
    (S : Finset ℕ) (H : ℕ)
    (hwindows : ∀ x ∈ S, f 0 < x ∧ x + H ≤ f (k - 1) ∧
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 3 < p ∧ 3 < q ∧
        f (k - 1) < 3 * p ∧ f (k - 1) < 3 * q ∧
        x ≤ p ∧ p < x + H ∧ x ≤ 2 * q ∧ 2 * q < x + H) :
    S.card ≤ H * ((Finset.range (k - 1)).filter (fun i => f (i + 1) - f i = 1)).card := by
  classical
  have hdist (i j : ℕ) (hi : i < k) (hj : j < k) (hne : i ≠ j) : f i ≠ f j := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact (hmono i j h hj).ne
    · exact (hmono j i h hi).ne'
  have hbound (i : ℕ) (hi : i < k) : f i ≤ f (k - 1) := by
    rcases eq_or_lt_of_le (show i ≤ k - 1 by omega) with rfl | h
    · rfl
    exact (hmono i (k - 1) h (by omega)).le
  have hordered {a b : ℕ} (ha : f 0 < a) (hb : b < f (k - 1)) (hab : a < b)
      (hpar : a % 2 ≠ b % 2)
      (hma : ∀ i, i < k → f i ≠ a) (hmb : ∀ i, i < k → f i ≠ b) :
      ∃ i, i + 1 < k ∧ f (i + 1) - f i = 1 ∧ a < f i ∧ f (i + 1) < b := by
    obtain ⟨j, hj, _, hja⟩ := neighbors_of_omission hk hgap ha (by omega) hma
    have hne : a + 1 ≠ b := by
      intro h
      exact hmb (j + 1) hj (hja.trans h)
    exact interval_contains_unit_gap hk hmono hgap ha hb (by omega) hpar hma hmb
  have hchoose (x : S) :
      ∃ i, i + 1 < k ∧ f (i + 1) - f i = 1 ∧ x.val ≤ f i ∧ f i < x.val + H := by
    obtain ⟨hx, hhi, p, q, hp, hq, hp3, hq3, hpM, hqM, hxp, hpx, hxq, hqx⟩ :=
      hwindows x.val x.property
    have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
    have hmissp (i : ℕ) (hi : i < k) (he : f i = p) : False := by
      apply Erdos287.no_denominator_multiple_of_large_prime_above_third
        k hk f hf1 hsum hdist (f (k - 1)) hbound p hp hp3 hpM i hi
      rw [he]
    have hmissq (i : ℕ) (hi : i < k) (he : f i = 2 * q) : False := by
      apply Erdos287.no_denominator_multiple_of_large_prime_above_third
        k hk f hf1 hsum hdist (f (k - 1)) hbound q hq hq3 hqM i hi
      exact ⟨2, by omega⟩
    have hpar : p % 2 ≠ (2 * q) % 2 := by omega
    have hgood : ∃ i, i + 1 < k ∧ f (i + 1) - f i = 1 ∧
        min p (2 * q) < f i ∧ f (i + 1) < max p (2 * q) := by
      rcases lt_or_gt_of_ne (show p ≠ 2 * q by omega) with h | h
      · simpa only [min_eq_left h.le, max_eq_right h.le] using
          hordered (by omega) (by omega) h hpar hmissp hmissq
      · simpa only [min_eq_right h.le, max_eq_left h.le] using
          hordered (by omega) (by omega) h hpar.symm hmissq hmissp
    obtain ⟨i, hi, hd, hlo, hup⟩ := hgood
    have hfi := hmono i (i + 1) (by omega) hi
    have hlo' : x.val ≤ min p (2 * q) := le_min hxp hxq
    have hup' : max p (2 * q) < x.val + H := max_lt hpx hqx
    exact ⟨i, hi, hd, by omega, by omega⟩
  choose pick hPick using hchoose
  let g (x : ℕ) : ℕ := if hx : x ∈ S then pick ⟨x, hx⟩ else 0
  have hg {x : ℕ} (hx : x ∈ S) :
      g x + 1 < k ∧ f (g x + 1) - f (g x) = 1 ∧ x ≤ f (g x) ∧ f (g x) < x + H := by
    simpa only [g, dif_pos hx] using hPick ⟨x, hx⟩
  refine Finset.card_le_mul_card_image_of_maps_to (f := g) ?_ H ?_
  · intro x hx
    have ⟨hik, hd, _, _⟩ := hg hx
    exact mem_filter.mpr ⟨mem_range.mpr (by omega), hd⟩
  · intro i _
    have hsub : S.filter (fun x => g x = i) ⊆ Ioc (f i - H) (f i) := by
      intro x hx
      obtain ⟨hx, hxi⟩ := mem_filter.mp hx
      obtain ⟨_, _, hxl, hxu⟩ := hg hx
      rw [hxi] at hxl hxu
      have hxpos := (hwindows x hx).1
      exact mem_Ioc.mpr ⟨by omega, hxl⟩
    exact (card_le_card hsub).trans (by rw [Nat.card_Ioc]; omega)

