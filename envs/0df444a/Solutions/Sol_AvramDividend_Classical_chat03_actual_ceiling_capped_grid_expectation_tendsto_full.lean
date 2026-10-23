-- Prove2me | solution 1 for AvramDividend.Classical.chat03_actual_ceiling_capped_grid_expectation_tendsto_full
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T07:11:43.187844+00:00
-- url     : https://prove2.me/submissions/53719f6c-ca99-42c4-a267-49b38b28a37c

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_actual_ceiling_capped_grid_scale_limit_aestrongly_measurable
import Theorems.Thm_AvramDividend_Classical_chat03_actual_ceiling_capped_grid_expectation_tendsto
import Mathlib.Probability.Process.HittingTime

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal

/-!
Actual first-passage grid expectations converge to the stopped
q-scale expectation with every measurability hypothesis discharged.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (θ x : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ)
    (lower upper : ℝ) (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτ : ∀ᵐ ω ∂P, IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} (τ ω))
    (mesh : ℕ → ℝ≥0) (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ n, 0 < mesh n)
    (K : ℕ → Ω → ℕ)
    (hK : ∀ n η, K n η = hittingBtwn
      (fun (j : ℕ) ξ => max
        (X.X ((j : ℝ≥0) * mesh n) ξ - upper)
        (lower - X.X ((j : ℝ≥0) * mesh n) ξ))
      (Set.Ioi (0 : ℝ)) 0 (Nat.ceil (T / mesh n)) η) :
    Integrable (fun ω =>
      Real.exp (-(q * ((min (τ ω) T) : ℝ))) *
        W (x + X.X (min (τ ω) T) ω)) P ∧
    Tendsto (fun n => ∫ ω,
      Real.exp (-(q * ((min ((K n ω : ℝ≥0) * mesh n) T) : ℝ))) *
        W (x + X.X (min ((K n ω : ℝ≥0) * mesh n) T) ω) ∂P)
      atTop (𝓝 (∫ ω,
        Real.exp (-(q * ((min (τ ω) T) : ℝ))) *
          W (x + X.X (min (τ ω) T) ω) ∂P)) := by
  have hZ :=
    chat03_actual_ceiling_capped_grid_scale_limit_aestrongly_measurable
      X q W hW hzero x lower upper T τ hτ mesh hmesh hpos K hK
  exact chat03_actual_ceiling_capped_grid_expectation_tendsto
    X q hq W hW hzero θ x hθ hψ
    lower upper T τ hτ mesh hmesh hpos K hK hZ
