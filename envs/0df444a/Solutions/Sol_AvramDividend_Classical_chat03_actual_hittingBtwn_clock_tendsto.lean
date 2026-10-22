-- Prove2me | solution 1 for AvramDividend.Classical.chat03_actual_hittingBtwn_clock_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T14:36:00.899597+00:00
-- url     : https://prove2.me/submissions/99275e4e-331a-4dc3-8705-58082fa9c7d4

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_actual_hittingBtwn_eventually_first_strict_grid_crossing
import Theorems.Thm_AvramDividend_Classical_chat03_first_grid_strict_exit_approaches_infimum
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Probability.Process.HittingTime

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal
open AvramDividend.Classical

/-!
The actual bounded Mathlib hittingBtwn first-exit clock on a vanishing
uniform grid converges to the finite continuous strict-passage infimum.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ) (τ : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ n, 0 < mesh n)
    (m : ℕ → ℕ)
    (hcap : ∀ᶠ n in atTop, τ + 1 ≤ (m n : ℝ≥0) * mesh n)
    (K : ℕ → Ω → ℕ)
    (hK : ∀ n η, K n η = hittingBtwn
      (fun (j : ℕ) ξ => max (X.X ((j : ℝ≥0) * mesh n) ξ - upper)
        (lower - X.X ((j : ℝ≥0) * mesh n) ξ))
      (Set.Ioi (0 : ℝ)) 0 (m n) η) :
    Tendsto (fun n => (K n ω : ℝ≥0) * mesh n) atTop (𝓝 τ) := by
  have hfirst :=
    chat03_actual_hittingBtwn_eventually_first_strict_grid_crossing
      X ω lower upper τ hτ mesh hmesh hpos m hcap K hK
  have hbracket (ε : ℝ≥0) (hε : 0 < ε) :
      ∀ᶠ n in atTop,
        τ ≤ (K n ω : ℝ≥0) * mesh n ∧
        (K n ω : ℝ≥0) * mesh n < τ + ε := by
    obtain ⟨δ, hδ, hgrid⟩ :=
      chat03_first_grid_strict_exit_approaches_infimum
        X ω lower upper τ hτ ε hε
    have hsmall : ∀ᶠ n in atTop, mesh n < δ :=
      (tendsto_order.1 hmesh).2 δ hδ
    filter_upwards [hsmall, hfirst] with n hn hfn
    obtain ⟨k, hkτ, hkε, hk, hbefore⟩ :=
      hgrid (mesh n) (hpos n) hn
    have hle : K n ω ≤ k := by
      by_contra h
      exact hfn.2 k (Nat.lt_of_not_ge h) hk
    have hge : k ≤ K n ω := by
      by_contra h
      exact hbefore (K n ω) (Nat.lt_of_not_ge h) hfn.1
    have heq : K n ω = k := le_antisymm hle hge
    simpa only [heq] using And.intro hkτ hkε
  apply tendsto_order.2
  constructor
  · intro a ha
    have hnear := hbracket 1 (show (0 : ℝ≥0) < 1 from zero_lt_one)
    filter_upwards [hnear] with n hn
    exact lt_of_lt_of_le ha hn.1
  · intro a ha
    have hε : 0 < a - τ := tsub_pos_of_lt ha
    have hnear := hbracket (a - τ) hε
    filter_upwards [hnear] with n hn
    simpa [add_tsub_cancel_of_le (le_of_lt ha)] using hn.2
