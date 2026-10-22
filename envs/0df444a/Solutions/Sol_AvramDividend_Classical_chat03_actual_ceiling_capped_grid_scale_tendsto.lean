-- Prove2me | solution 1 for AvramDividend.Classical.chat03_actual_ceiling_capped_grid_scale_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T21:12:38.720729+00:00
-- url     : https://prove2.me/submissions/b5f67572-99d2-4af5-b399-fba0b93b920f

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_actual_bounded_grid_scale_tendsto_at_terminal_horizon
import Theorems.Thm_AvramDividend_Classical_chat03_terminal_ceiling_cap_before_later_exit
import Theorems.Thm_AvramDividend_Classical_chat03_nnreal_grid_ceiling_bracket
import Mathlib.Probability.Process.HittingTime
import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal
open AvramDividend.Classical

/-!
Exact capped-grid scale reward converges at a fixed finite horizon
when the cap is the ceiling-grid index. Both cap assumptions of the
underlying terminal-horizon theorem follow from the ceiling bracket.
The continuous exit infimum must differ from the horizon.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (ω : Ω) (lower upper x : ℝ) (τ T : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (hbranch : τ < T ∨ T < τ)
    (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ n, 0 < mesh n)
    (K : ℕ → Ω → ℕ)
    (hK : ∀ n η, K n η = hittingBtwn
      (fun (j : ℕ) ξ => max
        (X.X ((j : ℝ≥0) * mesh n) ξ - upper)
        (lower - X.X ((j : ℝ≥0) * mesh n) ξ))
      (Set.Ioi (0 : ℝ)) 0 (Nat.ceil (T / mesh n)) η) :
    Tendsto (fun n =>
      Real.exp (-(q * ((min ((K n ω : ℝ≥0) * mesh n) T) : ℝ))) *
        W (x + X.X (min ((K n ω : ℝ≥0) * mesh n) T) ω))
      atTop
      (𝓝 (Real.exp (-(q * ((min τ T) : ℝ))) *
        W (x + X.X (min τ T) ω))) := by
  have hcapT :
      ∀ᶠ n in atTop,
        T ≤ (Nat.ceil (T / mesh n) : ℝ≥0) * mesh n := by
    filter_upwards with n
    exact (chat03_nnreal_grid_ceiling_bracket
      T (mesh n) (hpos n)).1
  have hcapAfter (hafter : T < τ) :
      ∀ᶠ n in atTop,
        (Nat.ceil (T / mesh n) : ℝ≥0) * mesh n < τ := by
    filter_upwards
      [chat03_terminal_ceiling_cap_before_later_exit
        T τ hafter mesh hmesh hpos] with n hn
    exact hn.2
  exact chat03_actual_bounded_grid_scale_tendsto_at_terminal_horizon
    X q W hW hzero ω lower upper x τ T hτ hbranch
    mesh hmesh hpos (fun n => Nat.ceil (T / mesh n))
    hcapT hcapAfter K hK
