-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_22_original_BV_physical_stopped_generator_product_L1_to_random_expectation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T07:04:48.845482+00:00
-- url     : https://prove2.me/submissions/5f914ba9-e0a0-4f5d-941b-d42904beeaac

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

/-- The actual BV generator on the original time-product law has an integrable random clock integral and the exact Fubini expectation identity. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [SFinite P] {𝓕 : Filtration ℝ≥0 mΩ}
  (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
  (q : ℝ) (w : ℝ → ℝ) (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
  (T : ℝ≥0) (μT : Measure ℝ≥0) [SFinite μT]
  (hTime : μT = (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal))
  (E : Set (ℝ≥0 × Ω))
  (F : (ℝ≥0 × Ω) → ℝ)
  (hF : ∀ p, F p = if p ∈ E then
    Real.exp (-(q * (p.1 : ℝ))) *
      (X.drift * deriv w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) +
      (∫ z in Iio (0 : ℝ),
        w (Function.leftLim (fun s : ℝ≥0 =>
            x + X.X s p.2 - rightLimit D s p.2) p.1 + z) -
        w (Function.leftLim (fun s : ℝ≥0 =>
            x + X.X s p.2 - rightLimit D s p.2) p.1) ∂X.ν) -
      q * w (Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.2 - rightLimit D s p.2) p.1)) else 0)
  (hFI : Integrable F (μT.prod P))
  (Gdrift : Ω → ℝ)
  (hGDef : ∀ᵐ ω ∂P, Gdrift ω = ∫ t, F (t, ω) ∂μT) :
  Integrable Gdrift P ∧
    (∫ ω, Gdrift ω ∂P) = (∫ p, F p ∂(μT.prod P)) := by
  have hRandom : Integrable (fun ω => ∫ t, F (t, ω) ∂μT) P :=
    hFI.integral_prod_right
  have hGI : Integrable Gdrift P :=
    hRandom.congr (Filter.EventuallyEq.symm hGDef)
  refine ⟨hGI, ?_⟩
  calc
    (∫ ω, Gdrift ω ∂P) = (∫ ω, ∫ t, F (t, ω) ∂μT ∂P) :=
      integral_congr_ae hGDef
    _ = (∫ p, F p ∂(μT.prod P)) := (integral_prod_symm F hFI).symm
