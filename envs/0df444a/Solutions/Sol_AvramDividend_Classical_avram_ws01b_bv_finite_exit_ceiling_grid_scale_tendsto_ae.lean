-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01b_bv_finite_exit_ceiling_grid_scale_tendsto_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T11:32:25.086201+00:00
-- url     : https://prove2.me/submissions/a8166c4c-9c09-4aba-a62e-c6fd23c46ded

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_stopped_scale_continuity_ae
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_finite_two_sided_min_isGLB
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_actual_ceiling_capped_grid_scale_tendsto_of_continuity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- The true BV two-sided first-grid payoff converges on every finite-exit trajectory. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (T : ℝ≥0) (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (𝓝 0)) (hpos : ∀ n, 0 < mesh n)
    (K : ℕ → Ω → ℕ)
    (hK : ∀ n η, K n η = hittingBtwn
      (fun (j : ℕ) ξ => max
        (X.X ((j : ℝ≥0) * mesh n) ξ - (a-x))
        ((-x) - X.X ((j : ℝ≥0) * mesh n) ξ))
      (Set.Ioi (0 : ℝ)) 0 (Nat.ceil (T / mesh n)) η) :
    ∀ᵐ ω ∂P,
      min (twoSidedExitUpTime X (a-x) ω)
        (twoSidedExitDownTime X (-x) ω) < ⊤ →
      Tendsto (fun n =>
        Real.exp (-(q * ((min ((K n ω : ℝ≥0) * mesh n) T) : ℝ))) *
          W (x + X.X (min ((K n ω : ℝ≥0) * mesh n) T) ω))
        atTop
        (𝓝 (Real.exp (-(q * ((min
          (min (twoSidedExitUpTime X (a-x) ω)
            (twoSidedExitDownTime X (-x) ω)).toNNReal T) : ℝ))) *
          W (x + X.X (min
            (min (twoSidedExitUpTime X (a-x) ω)
              (twoSidedExitDownTime X (-x) ω)).toNNReal T) ω))) := by
  have hC := avram_ws01b_bv_stopped_scale_continuity_ae
    X hX q hq W hW hBV a x ha hx0 hxa
  filter_upwards [hC] with ω hCω
  intro hfinite
  have hGLB :=
    avram_ws01b_finite_two_sided_min_isGLB
      X ω (-x) (a-x) hfinite
  exact avram_ws01b_actual_ceiling_capped_grid_scale_tendsto_of_continuity
    X q W hW ω (-x) (a-x) x
      (min (twoSidedExitUpTime X (a-x) ω)
        (twoSidedExitDownTime X (-x) ω)).toNNReal
      T hGLB (fun _ => hCω hfinite) mesh hmesh hpos K hK
