-- Prove2me | solution 1 for Diaz.outer_multiplier_param
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T07:15:44.799754+00:00
-- url     : https://prove2.me/submissions/c153d0e4-b93d-4e0d-9b10-32f69b2ae4e4

import Mathlib

open ComplexConjugate

theorem solution {u : ℂ} (hu0 : u ≠ 0) (S : Set ℂ) :
    {x : ℂ | x * u ∈ S ∧ x * conj u ∈ S}
      = (fun a => a * conj u / (u * conj u)) ''
        {a : ℂ | a ∈ S ∧ a * (conj u) ^ 2 / (u * conj u) ∈ S} := by
  have hcu : conj u ≠ 0 := by simpa using hu0
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨x * u, ⟨h1, ?_⟩, ?_⟩
    · have he : x * u * (conj u) ^ 2 / (u * conj u) = x * conj u := by field_simp <;> ring
      rw [he]; exact h2
    · field_simp
  · rintro ⟨a, ⟨ha1, ha2⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · have he : a * conj u / (u * conj u) * u = a := by field_simp <;> ring
      rw [he]; exact ha1
    · have he : a * conj u / (u * conj u) * conj u = a * (conj u) ^ 2 / (u * conj u) := by
        field_simp <;> ring
      rw [he]; exact ha2
