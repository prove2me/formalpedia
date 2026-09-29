-- Prove2me | solution 1 for Freiman.other22_context_cover
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T21:24:14.786237+00:00
-- url     : https://prove2.me/submissions/e1773bde-660a-49e5-99a2-cac826c26a62

import Definitions.Def_Freiman_other22Verification
import Mathlib.Tactic

open Freiman

private theorem cores_last : ∀ c ∈ lowerCores,
    (c.1.getLast? = some 1 ∨ c.1.getLast? = some 2 ∨ c.1.getLast? = some 3) ∧
    (c.2.getLast? = some 1 ∨ c.2.getLast? = some 2 ∨ c.2.getLast? = some 3) := by decide

private theorem small_suffix (core tail : List ℕ+)
    (hc : core.getLast? = some 1 ∨ core.getLast? = some 2 ∨ core.getLast? = some 3)
    (ht : ∀ d ∈ tail, (d : ℕ) ≤ 3) :
    ∃ d : ℕ+, (d = 1 ∨ d = 2 ∨ d = 3) ∧ ([d] : List ℕ+) <:+ core ++ tail := by
  rcases eq_or_ne tail [] with rfl | hne
  · rcases hc with h | h | h
    · exact ⟨1, Or.inl rfl, by simpa using List.singleton_suffix_iff_getLast?_eq_some.mpr h⟩
    · exact ⟨2, Or.inr (Or.inl rfl), by
        simpa using List.singleton_suffix_iff_getLast?_eq_some.mpr h⟩
    · exact ⟨3, Or.inr (Or.inr rfl), by
        simpa using List.singleton_suffix_iff_getLast?_eq_some.mpr h⟩
  · set d := tail.getLast hne with hdef
    have hmem : d ∈ tail := List.getLast_mem hne
    have hle : (d : ℕ) ≤ 3 := ht d hmem
    have hge : 1 ≤ (d : ℕ) := d.property
    have hsuf : ([d] : List ℕ+) <:+ core ++ tail :=
      (List.singleton_suffix_iff_getLast?_eq_some.mpr
        (List.getLast?_eq_some_getLast hne)).trans (List.suffix_append core tail)
    refine ⟨d, ?_, hsuf⟩
    interval_cases h : (d : ℕ)
    · exact Or.inl (PNat.coe_injective (by simpa using h))
    · exact Or.inr (Or.inl (PNat.coe_injective (by simpa using h)))
    · exact Or.inr (Or.inr (PNat.coe_injective (by simpa using h)))

private theorem last_unique (w : List ℕ+) (a b : ℕ+)
    (ha : ([a] : List ℕ+) <:+ w) (hb : ([b] : List ℕ+) <:+ w) : a = b := by
  have h1 := List.singleton_suffix_iff_getLast?_eq_some.mp ha
  have h2 := List.singleton_suffix_iff_getLast?_eq_some.mp hb
  rw [h1] at h2
  exact Option.some_inj.mp h2

theorem solution (Z B R S : LowerPair) (h : LowerOther22Geometry Z B R S) :
    ∃ k : Fin 6, lowerHistoryContextFits Z (other22Context k) := by
  obtain ⟨c, hc, u, v, hp, hu, hv⟩ := h.admissibleZ.1
  obtain ⟨hc1, -⟩ := cores_last c hc
  obtain ⟨d, hd, hsuf⟩ : ∃ d : ℕ+, (d = 1 ∨ d = 2 ∨ d = 3) ∧ ([d] : List ℕ+) <:+ Z.1 := by
    rw [hp]; exact small_suffix _ _ hc1 hu
  have hno : ∀ a b : ℕ+, a ≠ b → ([a] : List ℕ+) <:+ Z.1 → ¬ (([b] : List ℕ+) <:+ Z.1) :=
    fun a b hab ha hb => hab (last_unique Z.1 a b ha hb)
  have h31to1 : ∀ w : List ℕ+, ([3,1] : List ℕ+) <:+ w → ([1] : List ℕ+) <:+ w :=
    fun w hw => List.IsSuffix.trans (by decide) hw
  have e1 : ¬ (([3] : List ℕ+) <:+ [3,1]) := by decide
  have e2 : ([3,1] : List ℕ+) <:+ [3,1] := by decide
  have e3 : ¬ (([3] : List ℕ+) <:+ [1]) := by decide
  have e4 : ¬ (([3,1] : List ℕ+) <:+ [1]) := by decide
  have e5 : ¬ (([3] : List ℕ+) <:+ [2]) := by decide
  have e6 : ¬ (([3,1] : List ℕ+) <:+ [2]) := by decide
  have e7 : ([3] : List ℕ+) <:+ [3] := by decide
  have e8 : ¬ (([3,1] : List ℕ+) <:+ [3]) := by decide
  -- the right word ends with [3,1], hence with 1, hence not with 3
  have hr31 : ([3,1] : List ℕ+) <:+ Z.2 := h.right31
  have hrno3 : ¬ (([3] : List ℕ+) <:+ Z.2) := fun h3 =>
    absurd (last_unique Z.2 3 1 h3 (h31to1 _ hr31)) (by decide)
  have hright : lowerHistorySuffixContext Z.2 [3,1] :=
    ⟨hr31, ⟨fun h3 => absurd h3 hrno3, fun h3 => absurd h3 e1⟩, ⟨fun _ => e2, fun _ => hr31⟩⟩
  have hpar : (decide (Z.1.length % 2 = 1)).xor false
      = (decide (Z.2.length % 2 = 1)).xor false := by rw [h.equalZ]
  rcases hd with rfl | rfl | rfl
  · by_cases h31 : ([3,1] : List ℕ+) <:+ Z.1
    · exact ⟨3, ⟨h31,
        ⟨fun h3 => absurd (last_unique Z.1 3 1 h3 hsuf) (by decide), fun h3 => absurd h3 e1⟩,
        ⟨fun _ => e2, fun _ => h31⟩⟩, hright, hpar⟩
    · exact ⟨0, ⟨hsuf,
        ⟨fun h3 => absurd (last_unique Z.1 3 1 h3 hsuf) (by decide), fun h3 => absurd h3 e3⟩,
        ⟨fun hx => absurd hx h31, fun hx => absurd hx e4⟩⟩, hright, hpar⟩
  · exact ⟨1, ⟨hsuf,
      ⟨fun h3 => absurd (last_unique Z.1 3 2 h3 hsuf) (by decide), fun h3 => absurd h3 e5⟩,
      ⟨fun hx => absurd (last_unique Z.1 1 2 (h31to1 _ hx) hsuf) (by decide),
        fun hx => absurd hx e6⟩⟩, hright, hpar⟩
  · exact ⟨2, ⟨hsuf, ⟨fun _ => e7, fun _ => hsuf⟩,
      ⟨fun hx => absurd (last_unique Z.1 1 3 (h31to1 _ hx) hsuf) (by decide),
        fun hx => absurd hx e8⟩⟩, hright, hpar⟩
