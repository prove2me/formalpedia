-- Prove2me | solution 1 for Erdos287.consecutive_runs_from_denominator_density
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T10:01:32.488728+00:00
-- url     : https://prove2.me/submissions/59f23228-be6e-4fbb-9882-8ba29ba0cff7

import Mathlib

open Finset

set_option autoImplicit false

/-- Every omitted denominator rules out at most `w` starts of fully selected
intervals of length `w`. -/
theorem solution (m M w : ℕ) (_hw : 1 ≤ w) (hwM : w ≤ M + 1)
    (T : Finset ℕ) (hT : T ⊆ Finset.Icc m M) :
    let R := (Finset.Icc m (M + 1 - w)).filter (fun x => ∀ i ∈ Finset.range w, x + i ∈ T)
    M + 2 ≤ m + w + w * (M + 1 - m - T.card) + R.card := by
  classical
  dsimp only
  let starts := Icc m (M + 1 - w)
  let good := starts.filter (fun x => ∀ i ∈ range w, x + i ∈ T)
  let holes := Icc m M \ T
  let blocked (i : ℕ) := holes.image (fun y => y - i)
  have hcover : starts \ good ⊆ (range w).biUnion blocked := by
    intro x hx
    obtain ⟨hxStart, hxBad⟩ := mem_sdiff.mp hx
    have hxBounds := mem_Icc.mp hxStart
    have hno : ¬∀ i ∈ range w, x + i ∈ T := by
      intro hall
      exact hxBad (mem_filter.mpr ⟨hxStart, hall⟩)
    push Not at hno
    obtain ⟨i, hi, hmiss⟩ := hno
    have hiw := mem_range.mp hi
    have hhole : x + i ∈ holes := mem_sdiff.mpr
      ⟨mem_Icc.mpr ⟨by omega, by omega⟩, hmiss⟩
    exact mem_biUnion.mpr ⟨i, hi, mem_image.mpr ⟨x + i, hhole, by omega⟩⟩
  have hbad : (starts \ good).card ≤ w * holes.card := calc
    _ ≤ ((range w).biUnion blocked).card := card_le_card hcover
    _ ≤ ∑ i ∈ range w, (blocked i).card := card_biUnion_le
    _ ≤ ∑ _i ∈ range w, holes.card := sum_le_sum fun _ _ => card_image_le
    _ = _ := by simp
  have hsplit : (starts \ good).card = starts.card - good.card :=
    card_sdiff_of_subset (filter_subset _ _)
  have hholes : holes.card = M + 1 - m - T.card := by
    rw [show holes = Icc m M \ T from rfl, card_sdiff_of_subset hT, Nat.card_Icc]
  have hstarts : starts.card = M + 1 - w + 1 - m := Nat.card_Icc _ _
  change M + 2 ≤ m + w + w * (M + 1 - m - T.card) + good.card
  rw [hsplit, hstarts, hholes] at hbad
  omega

