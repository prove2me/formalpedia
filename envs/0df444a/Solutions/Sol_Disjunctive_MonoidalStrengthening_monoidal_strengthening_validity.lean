-- Prove2me | solution 1 for Disjunctive.MonoidalStrengthening.monoidal_strengthening_validity
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T22:52:34.374355+00:00
-- url     : https://prove2.me/submissions/35787887-b275-47bb-8f6b-6a15eb82a454

import Mathlib
import Definitions.Def_Disjunctive_MonoidalStrengthening_Basic

open Disjunctive.MonoidalStrengthening in
theorem solution : ¬ (∀ {q n : ℕ}
    (a : Fin q → Fin n → ℝ) (a0 b : Fin q → ℝ) (J1 : Finset (Fin n))
    (m : Fin n → Fin q → ℤ) (hm_mem : ∀ j ∈ J1, (fun i => m j i) ∈ CutMonoid q)
    (x : Fin n → ℝ) (hx_nonneg : 0 ≤ x) (hx_int : ∀ j ∈ J1, ∃ k : ℤ, x j = (k : ℝ))
    (hx_lb : ∀ i, b i ≤ ∑ j, a i j * x j)
    (hx_disj : ∃ i, a0 i ≤ ∑ j, a i j * x j),
    ∃ i, a0 i ≤ ∑ j ∈ J1, (a i j + (a0 i - b i) * (m j i : ℝ)) * x j +
      ∑ j ∈ Finset.univ \ J1, a i j * x j) := by
  intro h
  obtain ⟨i, hi⟩ := @h 1 1 (fun _ _ => 1) (fun _ => 1) (fun _ => 3) Finset.univ
    (fun _ _ => 1)
    (by intro j _; simp [CutMonoid])
    (fun _ => 3)
    (by intro j; simp only [Pi.zero_apply]; norm_num)
    (by intro j _; exact ⟨3, by norm_num⟩)
    (by intro i; simp)
    ⟨0, by simp⟩
  simp at hi
  norm_num at hi
