-- Prove2me | solution 1 for FiniteEnergyPlane.exists_ne_of_isNondegenerateEnd
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-03T11:59:32.649436+00:00
-- url     : https://prove2.me/submissions/a0112e65-2b88-4e34-acab-594d71d67ec5

import Definitions.Def_FiniteEnergyPlane_Asymptotics



namespace FiniteEnergyPlane

theorem exists_ne_of_isNondegenerateEnd_aux {n : ℕ} (H : V n → ℝ) (u : ℂ → V n)
    (e : ℝ → ℝ → ℂ) (P : ReebOrbit H) {ε : ℝ} (hε : ε ≠ 0)
    (hnd : IsNondegenerateEnd H u e P ε) : ∃ z₁ z₂, u z₁ ≠ u z₂ := by
  by_contra hc
  push_neg at hc
  obtain ⟨d, -, -, -, ha, -⟩ := hnd
  obtain ⟨s₀, hs₀⟩ := ha 1 one_pos
  set c : ℝ := aCoord H (u 0) with hcdef
  have hconst : ∀ s t : ℝ, endA H u e (s, t) = c := fun s t => by
    simp only [endA, hcdef, hc (e s t) 0]
  have hT := P.T_pos
  have hεp : 0 < |ε| := abs_pos.2 hε
  set s : ℝ := max (max s₀ 0) ((|c| + |d| + 2) / (|ε| * P.T)) with hsdef
  have hs0 : 0 ≤ s := le_trans (le_max_right _ _) (le_max_left _ _)
  have hs := hs₀ s (le_trans (le_max_left _ _) (le_max_left _ _)) 0
  dsimp only at hs
  rw [hconst, Real.norm_eq_abs] at hs
  have hsT : |c| + |d| + 2 ≤ |ε| * P.T * s := by
    have : (|c| + |d| + 2) / (|ε| * P.T) ≤ s := le_max_right _ _
    rwa [div_le_iff₀ (by positivity), mul_comm] at this
  have habs : |ε * P.T * s| = |ε| * P.T * s := by
    rw [abs_mul, abs_mul, abs_of_pos hT, abs_of_nonneg hs0]
  have htri : |ε * P.T * s| ≤ |c| + |d| + 1 := by
    have h1 : ε * P.T * s = c - d - (c - ε * P.T * s - d) := by ring
    rw [h1]
    calc |c - d - (c - ε * P.T * s - d)| ≤ |c - d| + |c - ε * P.T * s - d| := abs_sub _ _
      _ ≤ |c| + |d| + 1 := by linarith [abs_sub c d]
  linarith

end FiniteEnergyPlane

open FiniteEnergyPlane

theorem solution {n : ℕ} (H : V n → ℝ) (u : ℂ → V n)
    (e : ℝ → ℝ → ℂ) (P : ReebOrbit H) {ε : ℝ} (hε : ε ≠ 0)
    (hnd : IsNondegenerateEnd H u e P ε) : ∃ z₁ z₂, u z₁ ≠ u z₂ :=
  exists_ne_of_isNondegenerateEnd_aux H u e P hε hnd
