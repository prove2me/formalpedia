-- Prove2me | solution 1 for CompOT.DualAscent.proposition_3_5
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-13T21:24:30.197118+00:00
-- url     : https://prove2.me/submissions/2b636fed-fbcc-4a61-b7c4-9b6e5770e058

import Mathlib
import Definitions.Def_CompOT_DualAscent_Defs

theorem solution {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ) (f : Fin n → ℝ) (g : Fin m → ℝ)
    (hfg : CompOT.Duality.dualFeasible C f g) (S : Finset (Fin n)) (S' : Finset (Fin m))
    (hS : ∀ i ∈ S, ∀ j : Fin m, CompOT.DualAscent.Balanced C f g i j → j ∈ S') :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      CompOT.Duality.dualFeasible C (f + ε • CompOT.DualAscent.indicatorVec S)
        (g - ε • CompOT.DualAscent.indicatorVec S') := by
  classical
  -- slack of a pair
  set T : Finset (Fin n × Fin m) := Finset.univ.filter (fun p => p.1 ∈ S ∧ p.2 ∉ S') with hT
  have hslack : ∀ p ∈ T, 0 < C p.1 p.2 - f p.1 - g p.2 := by
    intro p hp
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    have hle := hfg p.1 p.2
    have hne : f p.1 + g p.2 ≠ C p.1 p.2 := fun h => hp.2 (hS p.1 hp.1 p.2 h)
    have := lt_of_le_of_ne hle hne
    linarith
  have key : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ p ∈ T, ε₀ ≤ C p.1 p.2 - f p.1 - g p.2 := by
    by_cases hne : T.Nonempty
    · obtain ⟨p, hp, hmin⟩ := T.exists_min_image (fun p => C p.1 p.2 - f p.1 - g p.2) hne
      exact ⟨_, hslack p hp, hmin⟩
    · refine ⟨1, one_pos, fun p hp => absurd ⟨p, hp⟩ hne⟩
  obtain ⟨ε₀, hε₀, hle⟩ := key
  refine ⟨ε₀, hε₀, fun ε hε hεε₀ i j => ?_⟩
  have hij := hfg i j
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, CompOT.DualAscent.indicatorVec]
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S'
  · simp [hi, hj]; linarith
  · have hmem : (i, j) ∈ T := by simp [hT, hi, hj]
    have := hle (i, j) hmem
    simp only at this
    simp [hi, hj]; linarith
  · simp [hi, hj]; linarith
  · simp [hi, hj]; linarith
