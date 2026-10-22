-- Prove2me | solution 1 for AvramDividend.Classical.chat03_actual_hittingBtwn_first_crossing_arbitrary_margin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T20:38:01.726652+00:00
-- url     : https://prove2.me/submissions/a2fd473a-30f6-49da-9511-7acd2d6c4f01

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_first_grid_crossing_before_arbitrary_terminal_margin
import Theorems.Thm_AvramDividend_Classical_chat03_hittingBtwn_eq_earliest_observed_crossing
import Mathlib.Probability.Process.HittingTime

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal
open AvramDividend.Classical

/-!
Identify the actual bounded hittingBtwn clock with the genuine minimal
strict first-grid crossing, eventually along any positive vanishing mesh
whose terminal horizon exceeds the passage infimum by any positive margin.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ) (τ ε : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (hε : 0 < ε)
    (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ n, 0 < mesh n)
    (m : ℕ → ℕ)
    (hcap : ∀ᶠ n in atTop, τ + ε ≤ (m n : ℝ≥0) * mesh n)
    (K : ℕ → Ω → ℕ)
    (hK : ∀ n η, K n η = hittingBtwn
      (fun (j : ℕ) ξ => max (X.X ((j : ℝ≥0) * mesh n) ξ - upper)
        (lower - X.X ((j : ℝ≥0) * mesh n) ξ))
      (Set.Ioi (0 : ℝ)) 0 (m n) η) :
    ∀ᶠ n in atTop,
      (X.X ((K n ω : ℝ≥0) * mesh n) ω < lower ∨
       upper < X.X ((K n ω : ℝ≥0) * mesh n) ω) ∧
      (∀ j : ℕ, j < K n ω →
        ¬ (X.X ((j : ℝ≥0) * mesh n) ω < lower ∨
           upper < X.X ((j : ℝ≥0) * mesh n) ω)) := by
  have hexists :=
    chat03_first_grid_crossing_before_arbitrary_terminal_margin
      X ω lower upper τ ε hτ hε mesh hmesh hpos m hcap
  filter_upwards [hexists] with n hn
  obtain ⟨k, hkm, hk, hkfirst⟩ := hn
  let u : ℕ → Ω → ℝ := fun j ξ =>
    max (X.X ((j : ℝ≥0) * mesh n) ξ - upper)
      (lower - X.X ((j : ℝ≥0) * mesh n) ξ)
  have hhit : u k ω ∈ Set.Ioi (0 : ℝ) := by
    change 0 < max (X.X ((k : ℝ≥0) * mesh n) ω - upper)
      (lower - X.X ((k : ℝ≥0) * mesh n) ω)
    rcases hk with hl | hu
    · exact lt_max_of_lt_right (sub_pos.mpr hl)
    · exact lt_max_of_lt_left (sub_pos.mpr hu)
  have hbefore : ∀ j : ℕ, j < k → u j ω ∉ Set.Ioi (0 : ℝ) := by
    intro j hj hjhit
    change 0 < max (X.X ((j : ℝ≥0) * mesh n) ω - upper)
      (lower - X.X ((j : ℝ≥0) * mesh n) ω) at hjhit
    rcases lt_max_iff.mp hjhit with hu | hl
    · exact hkfirst j hj (Or.inr (sub_pos.mp hu))
    · exact hkfirst j hj (Or.inl (sub_pos.mp hl))
  have heq : K n ω = k := by
    rw [hK n ω]
    exact chat03_hittingBtwn_eq_earliest_observed_crossing
      u (Set.Ioi (0 : ℝ)) ω (m n) k hkm hhit hbefore
  rw [heq]
  exact ⟨hk, hkfirst⟩