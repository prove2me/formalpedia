-- Prove2me | solution 1 for AvramDividend.Classical.chat03_actual_terminal_grid_scale_ae_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T21:07:39.592221+00:00
-- url     : https://prove2.me/submissions/4038806a-f60c-484c-bd20-12b2588fc8c7

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_actual_bounded_grid_scale_tendsto_at_terminal_horizon
import Mathlib.Probability.Process.HittingTime
import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal
open AvramDividend.Classical

/-!
Lift exact terminal-grid convergence from one sample path to almost
every sample path, preserving finite-horizon two-sided exit semantics.
The tie event τ=T is excluded almost everywhere and zero-scale at the
origin is explicit.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (lower upper x : ℝ) (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτ : ∀ᵐ ω ∂P,
      IsGLB
        {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} (τ ω))
    (hbranch : ∀ᵐ ω ∂P, τ ω < T ∨ T < τ ω)
    (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ n, 0 < mesh n)
    (m : ℕ → ℕ)
    (hcapT : ∀ᶠ n in atTop, T ≤ (m n : ℝ≥0) * mesh n)
    (hcapAfter : ∀ᵐ ω ∂P,
      T < τ ω →
        ∀ᶠ n in atTop, (m n : ℝ≥0) * mesh n < τ ω)
    (K : ℕ → Ω → ℕ)
    (hK : ∀ n η, K n η = hittingBtwn
      (fun (j : ℕ) ξ => max
        (X.X ((j : ℝ≥0) * mesh n) ξ - upper)
        (lower - X.X ((j : ℝ≥0) * mesh n) ξ))
      (Set.Ioi (0 : ℝ)) 0 (m n) η) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n =>
        Real.exp (-(q * ((min ((K n ω : ℝ≥0) * mesh n) T) : ℝ))) *
          W (x + X.X (min ((K n ω : ℝ≥0) * mesh n) T) ω))
        atTop
        (𝓝 (Real.exp (-(q * ((min (τ ω) T) : ℝ))) *
          W (x + X.X (min (τ ω) T) ω))) := by
  filter_upwards [hτ, hbranch, hcapAfter] with ω hτω hbranchω hafterω
  exact chat03_actual_bounded_grid_scale_tendsto_at_terminal_horizon
    X q W hW hzero ω lower upper x (τ ω) T hτω hbranchω
    mesh hmesh hpos m hcapT hafterω K hK
