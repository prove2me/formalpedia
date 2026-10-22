-- Prove2me | solution 1 for AvramDividend.Classical.chat03_actual_bounded_grid_discounted_scale_tendsto_of_Wzero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T14:33:56.23523+00:00
-- url     : https://prove2.me/submissions/8522dce1-28fe-4d1d-9981-06f76302fc6c

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_actual_hittingBtwn_eventually_first_strict_grid_crossing
import Theorems.Thm_AvramDividend_Classical_chat03_exponential_discount_first_grid_scale_tendsto
import Mathlib.Probability.Process.HittingTime

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal
open AvramDividend.Classical

/-!
Convergence of the exact exponentially discounted q-scale reward at the
actual measurable bounded hittingBtwn clock of a fine two-sided Lévy grid.
The zero-origin case uses accepted global q-scale continuity.
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
    Tendsto (fun n =>
      Real.exp (-(q * ((min ((K n ω : ℝ≥0) * mesh n) T) : ℝ))) *
        W (x + X.X (min ((K n ω : ℝ≥0) * mesh n) T) ω))
      atTop
      (𝓝 (Real.exp (-(q * ((min τ T) : ℝ))) *
        W (x + X.X (min τ T) ω))) := by
  have hfirst :=
    chat03_actual_hittingBtwn_eventually_first_strict_grid_crossing
      X ω lower upper τ hτ mesh hmesh hpos m hcap K hK
  exact chat03_exponential_discount_first_grid_scale_tendsto
    X q W hW hzero ω lower upper x τ T hτ
      mesh hmesh hpos (fun n => K n ω) hfirst
