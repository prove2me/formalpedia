-- Prove2me | solution 1 for AvramDividend.Classical.chat03_actual_bounded_grid_scale_tendsto_at_terminal_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T20:58:13.61988+00:00
-- url     : https://prove2.me/submissions/7d39b059-87bc-43cd-8c72-eb9cea54e36e

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_actual_bounded_grid_scale_tendsto_off_horizon_margin
import Mathlib.Probability.Process.HittingTime
import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal
open AvramDividend.Classical

/-!
Convergence of the actual finite-grid discounted scale reward at a
terminal horizon. A grid cap beyond T already contains a positive
margin beyond any continuous exit time strictly before T. The
after-horizon branch uses eventual grid clocks before the later exit.
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
    (m : ℕ → ℕ)
    (hcapT : ∀ᶠ n in atTop, T ≤ (m n : ℝ≥0) * mesh n)
    (hcapAfter : T < τ →
      ∀ᶠ n in atTop,
        (m n : ℝ≥0) * mesh n < τ)
    (K : ℕ → Ω → ℕ)
    (hK : ∀ n η, K n η = hittingBtwn
      (fun (j : ℕ) ξ => max
        (X.X ((j : ℝ≥0) * mesh n) ξ - upper)
        (lower - X.X ((j : ℝ≥0) * mesh n) ξ))
      (Set.Ioi (0 : ℝ)) 0 (m n) η) :
    Tendsto (fun n =>
      Real.exp (-(q * ((min ((K n ω : ℝ≥0) * mesh n) T) : ℝ))) *
        W (x + X.X (min ((K n ω : ℝ≥0) * mesh n) T) ω))
      atTop
      (𝓝 (Real.exp (-(q * ((min τ T) : ℝ))) *
        W (x + X.X (min τ T) ω))) := by
  rcases hbranch with hbefore | hafter
  · have hε : 0 < T - τ := tsub_pos_of_lt hbefore
    have hsum : τ + (T - τ) = T := by
      simpa only [add_comm] using
        (tsub_add_cancel_of_le (le_of_lt hbefore))
    have hcapBefore : τ < T →
        ∀ᶠ n in atTop,
          τ + (T - τ) ≤ (m n : ℝ≥0) * mesh n := by
      intro _
      filter_upwards [hcapT] with n hn
      simpa only [hsum] using hn
    exact chat03_actual_bounded_grid_scale_tendsto_off_horizon_margin
      X q W hW hzero (T - τ) hε ω lower upper x τ T hτ
      (Or.inl hbefore) mesh hmesh hpos m hcapBefore
      (fun h => hcapT.and (hcapAfter h)) K hK
  · have hcapBefore : τ < T →
        ∀ᶠ n in atTop,
          τ + (1 : ℝ≥0) ≤ (m n : ℝ≥0) * mesh n := by
      intro hb
      exact False.elim (not_lt_of_ge (le_of_lt hafter) hb)
    exact chat03_actual_bounded_grid_scale_tendsto_off_horizon_margin
      X q W hW hzero 1 (by exact zero_lt_one) ω lower upper x τ T hτ
      (Or.inr hafter) mesh hmesh hpos m hcapBefore
      (fun h => hcapT.and (hcapAfter h)) K hK
