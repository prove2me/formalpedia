-- Prove2me | solution 1 for AvramDividend.Classical.chat04_positive_reserve_killed_ennreal_nhds_of_psi_atTop
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T15:37:49.598743+00:00
-- url     : https://prove2.me/submissions/4c1da9ec-67e0-49cf-af39-9c17353e2fb0

import Theorems.Thm_AvramDividend_Classical_chat04_positive_reserve_killed_ennreal_expectation_nhds_no_schedule
import Theorems.Thm_AvramDividend_Classical_eventual_psi_above_q_of_tendsto_atTop
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology
open scoped NNReal ENNReal

/-- Derive ENNReal time-zero continuity from divergent Levy Laplace exponent. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : 0 < x)
    (hψdiv : Tendsto X.ψ atTop atTop) :
    Tendsto
      (fun t : ℝ≥0 => ∫⁻ ω,
        ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
          (fun u => ENNReal.ofReal
            (Real.exp (-(q * (t : ℝ))) * W (x + X.X t u))) ω ∂P)
      (𝓝 0) (𝓝 (ENNReal.ofReal (W x))) := by
  obtain ⟨θ, hθ, hlarge⟩ :=
    eventual_psi_above_q_of_tendsto_atTop X.ψ q hψdiv
  have hgap : q < X.ψ θ := hlarge θ le_rfl
  exact chat04_positive_reserve_killed_ennreal_expectation_nhds_no_schedule
    X q hq W hW θ x hθ hgap hx
