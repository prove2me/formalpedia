-- Prove2me | solution 1 for DiazModulus.binary_quadratic_dvd_of_coprime_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-01T09:33:19.146262+00:00
-- url     : https://prove2.me/submissions/aea70ebe-42b8-4a0f-a41e-8e0edfdc1eef

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # A quadratic coprime to `F` that divides `F · L` divides `L`, with the degree budget

Read `P`, `F`, `L`, `B` as binary forms of degrees `2`, `d`, `e`, `d + e − 2`; `hdeg` says that `P` and
`F` do not both vanish at `∞`. If `P = 0`, then `F` is a unit and `L = 0`. Otherwise `P ∣ F L` and
`IsCoprime P F` give `L = P L₀`; cancelling `P` gives `F L₀ = B`. If `deg P = 2`, then
`deg L = 2 + deg L₀ ≤ e`; if `deg F = d`, then `d + deg L₀ = deg B ≤ d + e − 2`. -/

open Polynomial in
theorem solution {K : Type*} [Field K] (P F L B : K[X]) (d e : ℕ)
    (hPF : IsCoprime P F) (hF0 : F ≠ 0) (hdeg : P.natDegree = 2 ∨ F.natDegree = d)
    (hL : L.natDegree ≤ e) (hB : B.natDegree + 2 ≤ d + e) (hFL : F * L = P * B) :
    ∃ L₀ : K[X], L = P * L₀ ∧ (L₀ = 0 ∨ L₀.natDegree + 2 ≤ e) := by
  by_cases hP0 : P = 0
  · subst hP0
    have hL0 : L = 0 := by simpa [hF0] using hFL
    exact ⟨0, by simp [hL0], Or.inl rfl⟩
  obtain ⟨L₀, rfl⟩ : P ∣ L := hPF.dvd_of_dvd_mul_left ⟨B, hFL⟩
  refine ⟨L₀, rfl, ?_⟩
  by_cases hL0 : L₀ = 0
  · exact Or.inl hL0
  right
  have hB' : F * L₀ = B := mul_left_cancel₀ hP0 (by rw [← hFL]; ring)
  rcases hdeg with h | h
  · have := natDegree_mul hP0 hL0
    omega
  · have := natDegree_mul hF0 hL0
    rw [hB'] at this
    omega
