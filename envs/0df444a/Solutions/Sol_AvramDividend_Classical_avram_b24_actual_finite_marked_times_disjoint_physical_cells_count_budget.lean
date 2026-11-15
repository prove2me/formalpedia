-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_actual_finite_marked_times_disjoint_physical_cells_count_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:41:14.82244+00:00
-- url     : https://prove2.me/submissions/aaffdc01-8147-4082-b33d-3a3acd1136c9

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    (S : Finset ℝ≥0) (I : Finset ℕ)
    (a b : ℕ → ℝ≥0)
    (hCells : ∀ i ∈ I, a i ≤ b i)
    (hDisjoint : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      Disjoint (Ioc (a i) (b i)) (Ioc (a j) (b j))) :
    (∑ i ∈ I,
      (S.filter (fun u => a i < u ∧ u ≤ b i)).card) ≤
        S.card := by
  classical
  let cell : ℕ → Finset ℝ≥0 := fun i =>
    S.filter (fun u => a i < u ∧ u ≤ b i)
  have hDisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      Disjoint (cell i) (cell j) := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro u hu hv
    have hu' : u ∈ Ioc (a i) (b i) :=
      (Finset.mem_filter.mp hu).2
    have hv' : u ∈ Ioc (a j) (b j) :=
      (Finset.mem_filter.mp hv).2
    exact Set.disjoint_left.mp (hDisjoint i hi j hj hij) hu' hv'
  have hUnion :
      (∑ i ∈ I, (cell i).card) = (I.biUnion cell).card := by
    symm
    exact Finset.card_biUnion hDisj
  have hSubset : I.biUnion cell ⊆ S := by
    intro u hu
    obtain ⟨i, hi, hui⟩ := Finset.mem_biUnion.mp hu
    exact (Finset.mem_filter.mp hui).1
  calc
    (∑ i ∈ I, (S.filter (fun u => a i < u ∧ u ≤ b i)).card) =
      (∑ i ∈ I, (cell i).card) := rfl
    _ = (I.biUnion cell).card := hUnion
    _ ≤ S.card := Finset.card_le_card hSubset
