-- Prove2me | solution 1 for CosmoConstCentury.einstein_static_universe_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T13:41:53.509986+00:00
-- url     : https://prove2.me/submissions/d596a81b-523f-421c-a81c-1fa03b511c2e

import Mathlib
import Definitions.Def_CosmoConstCentury_Defs

open Filter Topology

open CosmoConstCentury in
theorem solution (G c Λ R₀ ρ₀ : ℝ) (hR₀ : 0 < R₀) :
    IsFriedmannSolution G c Λ 1 Set.univ (fun _ => R₀) (fun _ => ρ₀) ↔
      (Λ = einsteinKappa G c * c ^ 2 * ρ₀ / 2 ∧ Λ = c ^ 2 / R₀ ^ 2) := by
  have hd : deriv (fun _ : ℝ => R₀) = fun _ => 0 := by
    funext t; simp
  constructor
  · intro h
    obtain ⟨-, -, h1, h2⟩ := h 0 (Set.mem_univ _)
    simp only [hd, deriv_const] at h1 h2
    have e2 : Λ = c ^ 2 / R₀ ^ 2 := by linear_combination -h2
    refine ⟨?_, e2⟩
    linear_combination (1 / 2 : ℝ) * h1 + (3 / 2 : ℝ) * e2
  · rintro ⟨e1, e2⟩ t -
    refine ⟨hR₀, contDiffAt_const, ?_, ?_⟩
    · simp only [hd, deriv_const]
      linear_combination (2 : ℝ) * e1 - 3 * e2
    · simp only [hd, deriv_const]
      linear_combination -e2
