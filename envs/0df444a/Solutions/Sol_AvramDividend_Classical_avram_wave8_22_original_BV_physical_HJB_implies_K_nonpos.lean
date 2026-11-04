-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_22_original_BV_physical_HJB_implies_K_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:18:57.133676+00:00
-- url     : https://prove2.me/submissions/b891609d-868d-498d-a6b2-dfbf9a62dce2

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- Original Lévy physical generator is nonpositive on the actual positive stopped region by source HJB and the positive discount factor. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [SFinite P] {𝓕 : Filtration ℝ≥0 mΩ}
  (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
  (q : ℝ) (w : ℝ → ℝ) (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
  (A : Ω → Set ℝ≥0)
  (K : ℝ≥0 → Ω → ℝ)
  (hK : ∀ t ω, K t ω =
    Real.exp (-(q * (t : ℝ))) *
      (X.drift * deriv w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) +
      (∫ z in Iio (0 : ℝ),
        w (Function.leftLim (fun s : ℝ≥0 =>
            x + X.X s ω - rightLimit D s ω) t + z) -
        w (Function.leftLim (fun s : ℝ≥0 =>
            x + X.X s ω - rightLimit D s ω) t) ∂X.ν) -
      q * w (Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s ω - rightLimit D s ω) t)))
  (hHJB : ∀ y : ℝ, 0 < y →
    X.drift * deriv w y +
      (∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν) -
      q * w y ≤ 0)
  (hPositive : ∀ᵐ ω ∂P, ∀ t, t ∈ A ω →
    0 < Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) :
  ∀ᵐ ω ∂P, ∀ t, t ∈ A ω → K t ω ≤ 0 := by
  filter_upwards [hPositive] with ω hp
  intro t ht
  have hSource := hHJB
    (Function.leftLim (fun s : ℝ≥0 =>
      x + X.X s ω - rightLimit D s ω) t) (hp t ht)
  rw [hK t ω]
  exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _) hSource
