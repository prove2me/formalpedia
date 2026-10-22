-- Prove2me | solution 1 for AvramDividend.Classical.chat03_actual_ceiling_capped_grid_scale_ae_all_branches
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T05:28:56.2+00:00
-- url     : https://prove2.me/submissions/337b9b4f-8527-48e3-9240-027b064e41a4

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_actual_ceiling_capped_grid_scale_tendsto_all_branches
import Mathlib.Probability.Process.HittingTime
import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal
open AvramDividend.Classical

/-!
The accepted pathwise trichotomy theorem lifts to almost-everywhere
convergence of the actual ceiling-capped discounted scale reward.
It allows atoms in the continuous exit time at T.
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
    (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ n, 0 < mesh n)
    (K : ℕ → Ω → ℕ)
    (hK : ∀ n η, K n η = hittingBtwn
      (fun (j : ℕ) ξ => max
        (X.X ((j : ℝ≥0) * mesh n) ξ - upper)
        (lower - X.X ((j : ℝ≥0) * mesh n) ξ))
      (Set.Ioi (0 : ℝ)) 0 (Nat.ceil (T / mesh n)) η) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n =>
        Real.exp (-(q * ((min ((K n ω : ℝ≥0) * mesh n) T) : ℝ))) *
          W (x + X.X (min ((K n ω : ℝ≥0) * mesh n) T) ω))
        atTop
        (𝓝 (Real.exp (-(q * ((min (τ ω) T) : ℝ))) *
          W (x + X.X (min (τ ω) T) ω))) := by
  filter_upwards [hτ] with ω hτω
  exact chat03_actual_ceiling_capped_grid_scale_tendsto_all_branches
    X q W hW hzero ω lower upper x (τ ω) T hτω
    mesh hmesh hpos K hK
