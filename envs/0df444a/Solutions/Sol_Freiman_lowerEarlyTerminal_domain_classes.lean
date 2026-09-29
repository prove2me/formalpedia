-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_domain_classes
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T21:11:45.482865+00:00
-- url     : https://prove2.me/submissions/bea6124a-6f8d-4c3e-ab16-1e8b03fd49b7

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry
import Mathlib.Tactic

set_option linter.unusedVariables false

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
    · exact ⟨1, Or.inl rfl, by
        simpa using List.singleton_suffix_iff_getLast?_eq_some.mpr h⟩
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
    · exact Or.inl (by exact_mod_cast PNat.coe_injective (by simpa using h))
    · exact Or.inr (Or.inl (PNat.coe_injective (by simpa using h)))
    · exact Or.inr (Or.inr (PNat.coe_injective (by simpa using h)))

private theorem index_of_digit (w : List ℕ+)
    (h : ∃ d : ℕ+, (d = 1 ∨ d = 2 ∨ d = 3) ∧ ([d] : List ℕ+) <:+ w) :
    ∃ i : Fin 3, lowerEnds w (lowerEarlyTerminalShortCatalog i).leftContext := by
  obtain ⟨d, hd, hsuf⟩ := h
  rcases hd with rfl | rfl | rfl
  · exact ⟨1, hsuf⟩
  · exact ⟨2, hsuf⟩
  · exact ⟨0, hsuf⟩

theorem solution (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hd : lowerEarlyDomain p) :
    ∃ i : Fin 3, lowerEnds (lowerNormalize p).1 (lowerEarlyTerminalShortCatalog i).leftContext := by
  obtain ⟨⟨⟨c, hc, u, v, hp, hu, hv⟩, -⟩, -, -, -⟩ := hs
  obtain ⟨hc1, hc2⟩ := cores_last c hc
  have h1 : ∃ d : ℕ+, (d = 1 ∨ d = 2 ∨ d = 3) ∧ ([d] : List ℕ+) <:+ p.1 := by
    rw [hp]; exact small_suffix _ _ hc1 hu
  have h2 : ∃ d : ℕ+, (d = 1 ∨ d = 2 ∨ d = 3) ∧ ([d] : List ℕ+) <:+ p.2 := by
    rw [hp]; exact small_suffix _ _ hc2 hv
  have hnorm : lowerNormalize p = p ∨ lowerNormalize p = (p.2,p.1) := by
    unfold lowerNormalize
    by_cases hw : lowerWidth p.2 ≤ lowerWidth p.1
    · exact Or.inl (by simp [hw])
    · exact Or.inr (by simp [hw])
  rcases hnorm with h | h <;> rw [h]
  · exact index_of_digit _ h1
  · exact index_of_digit _ h2
