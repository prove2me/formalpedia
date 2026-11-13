-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_finite_real_fibre_nat_enumeration_20261112
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T00:08:36.037198+00:00
-- url     : https://prove2.me/submissions/7626691f-b80d-4b22-8ce9-404fa5c98c96

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Finset
noncomputable section

/-- Finite real Borel mark fibres admit a natural-number enumeration
without changing their cardinality or conflating distinct fibres. -/
theorem solution
    (s : Finset ℝ) :
    ∃ u : ℕ → ℝ,
      (∀ i ∈ Finset.range s.card, u i ∈ s) ∧
      (∀ i ∈ Finset.range s.card,
        ∀ j ∈ Finset.range s.card, i ≠ j → u i ≠ u j) ∧
      (∀ y ∈ s, ∃ i ∈ Finset.range s.card, u i = y) := by
  classical
  let e : s ≃ Fin s.card := Finset.equivFin s
  let u : ℕ → ℝ := fun i =>
    if hi : i < s.card then (e.symm ⟨i, hi⟩).1 else 0
  refine ⟨u, ?_, ?_, ?_⟩
  · intro i hi
    have h : i < s.card := Finset.mem_range.mp hi
    simpa only [u, dif_pos h] using (e.symm ⟨i, h⟩).property
  · intro i hi j hj hij heq
    have h : i < s.card := Finset.mem_range.mp hi
    have h' : j < s.card := Finset.mem_range.mp hj
    have he : (e.symm ⟨i, h⟩).1 = (e.symm ⟨j, h'⟩).1 := by
      simpa only [u, dif_pos h, dif_pos h'] using heq
    have hsub : e.symm ⟨i, h⟩ = e.symm ⟨j, h'⟩ :=
      Subtype.ext he
    have hfin : (⟨i, h⟩ : Fin s.card) = ⟨j, h'⟩ :=
      e.symm.injective hsub
    exact hij (congrArg Fin.val hfin)
  · intro y hy
    let i : Fin s.card := e ⟨y, hy⟩
    refine ⟨i.1, Finset.mem_range.mpr i.2, ?_⟩
    change (if hi : i.1 < s.card then
      (e.symm ⟨i.1, hi⟩).1 else 0) = y
    simp only [dif_pos i.2]
    change (e.symm i).1 = y
    simp [i]
