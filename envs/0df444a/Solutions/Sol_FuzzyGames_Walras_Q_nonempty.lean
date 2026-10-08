-- Prove2me | solution 1 for FuzzyGames.Walras.Q_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T06:58:52.169457+00:00
-- url     : https://prove2.me/submissions/3f0833cc-a599-4960-b69e-2129043a9ca0

import Mathlib
import Definitions.Def_FuzzyGames_Walras_Basic

open FuzzyGames.Walras Set

theorem solution {n l : ℕ} (E : Economy n l) (hE : E.Assumptions)
    (xbar : Fin n → Fin l → ℝ) (hx : xbar ∈ E.X 1) (i : Fin n) :
    (E.Q xbar i).Nonempty := by
  -- Q(i) = Y(i) - {x | 0 ≤ x ∧ x ≻_i x̄^i}
  -- nonsatiation ⇒ preferred set nonempty; pos_endowed ⇒ Y(i) nonempty
  -- Minkowski difference of nonempty sets is nonempty
  obtain ⟨y, hyY, hypos⟩ := hE.pos_endowed i
  -- need 0 ≤ xbar i for nonsatiation premise
  have hxbar0 : 0 ≤ xbar i := by
    have : xbar ∈ E.X 1 := hx
    -- X τ requires ∀ i, 0 < τ i → 0 ≤ x i; here τ = 1
    have hX := this
    simp only [Economy.X, mem_setOf_eq] at hX
    have : (0 : ℝ) < (1 : Fin n → ℝ) i := by
      simp
    -- 1 as function is fun _ => 1
    change 0 ≤ xbar i
    exact hX.1 i (by simp)
  obtain ⟨x, hx0, hpref⟩ := hE.nonsatiation i (xbar i) hxbar0
  refine ⟨y - x, ?_⟩
  -- y - x ∈ Y i - preferred
  refine mem_sub.mpr ⟨y, hyY, x, ?_, rfl⟩
  exact ⟨hx0, hpref⟩
