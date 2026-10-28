-- Prove2me | solution 1 for AvramDividend.Classical.levy_capped_two_sided_first_exit_clock_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T09:45:14.022333+00:00
-- url     : https://prove2.me/submissions/59d6286d-aafe-4403-bff3-323b44612770

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_first_grid_capped_time_convergence
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.MeasureTheory.MeasurableSpace.Defs

open MeasureTheory Set Filter Topology
open scoped NNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Bounded first-crossing grid clocks converge to the clipped true exit clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ) (τ T : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ n, 0 < mesh n)
    (first : ℕ → ℕ)
    (hfirst : ∀ᶠ n in atTop,
      (X.X ((first n : ℝ≥0) * mesh n) ω < lower ∨
       upper < X.X ((first n : ℝ≥0) * mesh n) ω) ∧
      (∀ j : ℕ, j < first n →
        ¬ (X.X ((j : ℝ≥0) * mesh n) ω < lower ∨
           upper < X.X ((j : ℝ≥0) * mesh n) ω))) :
    Tendsto (fun n =>
      min ((first n : ℝ≥0) * mesh n) T) atTop (𝓝 (min τ T)) := by
  have hbracket (ε : ℝ≥0) (hε : 0 < ε) :
      ∀ᶠ n in atTop,
        min τ T ≤ min ((first n : ℝ≥0) * mesh n) T ∧
        min ((first n : ℝ≥0) * mesh n) T < min τ T + ε := by
    obtain ⟨δ, hδ, hgrid⟩ :=
      chat03_first_grid_capped_time_convergence
        X ω lower upper τ T hτ ε hε
    have hsmall : ∀ᶠ n in atTop, mesh n < δ :=
      (tendsto_order.1 hmesh).2 δ hδ
    filter_upwards [hsmall, hfirst] with n hn hfn
    obtain ⟨k, hk, hkfirst, hklo, hkhi⟩ :=
      hgrid (mesh n) (hpos n) hn
    have hle : first n ≤ k := by
      by_contra h
      exact hfn.2 k (Nat.lt_of_not_ge h) hk
    have hge : k ≤ first n := by
      by_contra h
      exact hkfirst (first n) (Nat.lt_of_not_ge h) hfn.1
    have heq : first n = k := le_antisymm hle hge
    simpa only [heq] using And.intro hklo hkhi
  apply tendsto_order.2
  constructor
  · intro a ha
    have hnear := hbracket 1 (show (0 : ℝ≥0) < 1 from zero_lt_one)
    filter_upwards [hnear] with n hn
    exact lt_of_lt_of_le ha hn.1
  · intro a ha
    have hε : 0 < a - min τ T := tsub_pos_of_lt ha
    have hnear := hbracket (a - min τ T) hε
    filter_upwards [hnear] with n hn
    simpa [add_tsub_cancel_of_le (le_of_lt ha)] using hn.2
