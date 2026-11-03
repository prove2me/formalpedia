-- Prove2me | solution 1 for FiniteEnergyPlane.exists_int_forall_mem_Ioo_of_forall_ne
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-02T16:01:24.460882+00:00
-- url     : https://prove2.me/submissions/ec38733d-94ac-48b2-876d-f50bbfaf66a3

import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Algebra.Order.Floor.Ring



namespace FiniteEnergyPlane

/-- A continuous real function on a preconnected space that never takes a value in the coset
`c + Lℤ` (`L > 0`) stays in one interval `(c + mL, c + (m + 1)L)`. -/
theorem exists_int_forall_mem_Ioo_of_forall_ne {X : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] [Nonempty X] (f : X → ℝ) (hf : Continuous f) (c L : ℝ) (hL : 0 < L)
    (h : ∀ x, ∀ m : ℤ, f x ≠ c + m * L) :
    ∃ m : ℤ, ∀ x, c + m * L < f x ∧ f x < c + (m + 1) * L := by
  obtain ⟨x₀⟩ := ‹Nonempty X›
  set m : ℤ := ⌊(f x₀ - c) / L⌋ with hm
  have hm1 : (m : ℝ) ≤ (f x₀ - c) / L := Int.floor_le _
  have hm2 : (f x₀ - c) / L < m + 1 := Int.lt_floor_add_one _
  have h1 : c + m * L ≤ f x₀ := by
    have := (le_div_iff₀ hL).1 hm1; linarith
  have h2 : f x₀ < c + (m + 1) * L := by
    have := (div_lt_iff₀ hL).1 hm2; linarith
  have h1' : c + m * L < f x₀ := lt_of_le_of_ne h1 (fun e => h x₀ m e.symm)
  refine ⟨m, fun x => ⟨?_, ?_⟩⟩
  · by_contra hx
    push_neg at hx
    have hmem : c + m * L ∈ Set.Icc (f x) (f x₀) := ⟨hx, h1'.le⟩
    obtain ⟨y, hy⟩ := intermediate_value_univ x x₀ hf hmem
    exact h y m hy
  · by_contra hx
    push_neg at hx
    have hmem : c + ((m + 1 : ℤ) : ℝ) * L ∈ Set.Icc (f x₀) (f x) := by
      push_cast; exact ⟨h2.le, hx⟩
    obtain ⟨y, hy⟩ := intermediate_value_univ x₀ x hf hmem
    exact h y (m + 1) hy

end FiniteEnergyPlane

open FiniteEnergyPlane

theorem solution {X : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] [Nonempty X] (f : X → ℝ) (hf : Continuous f) (c L : ℝ) (hL : 0 < L)
    (h : ∀ x, ∀ m : ℤ, f x ≠ c + m * L) :
    ∃ m : ℤ, ∀ x, c + m * L < f x ∧ f x < c + (m + 1) * L :=
  exists_int_forall_mem_Ioo_of_forall_ne f hf c L hL h
