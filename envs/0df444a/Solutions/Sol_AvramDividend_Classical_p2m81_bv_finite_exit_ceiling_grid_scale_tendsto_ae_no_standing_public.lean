-- Prove2me | solution 1 for AvramDividend.Classical.p2m81_bv_finite_exit_ceiling_grid_scale_tendsto_ae_no_standing_public
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T05:32:55.139196+00:00
-- url     : https://prove2.me/submissions/18d1aa96-cc6a-4d6d-8521-70dc4254544c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_p2m81_bv_stopped_scale_continuity_ae_no_standing_public
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_finite_two_sided_min_isGLB
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_actual_ceiling_capped_grid_scale_tendsto_of_continuity

open MeasureTheory Filter Set Topology
open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The Standing-free BV two-sided first-grid payoff converges on every finite-exit trajectory. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (W : ℝ → ℝ)
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
  have hC := p2m81_bv_stopped_scale_continuity_ae_no_standing_public
    X q φ hq hφ hroot W hW hBV a x ha hx0 hxa
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
