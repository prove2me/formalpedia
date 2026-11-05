-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_signed_GH_ae_sign_closed_under_clock_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:36:59.545397+00:00
-- url     : https://prove2.me/submissions/1d03b0d9-bed1-46c0-a04a-3de9e9de92d2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original stopped signed generator/dividend residual envelope remains nonpositive at an a.e. clock limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (Gk Hk : ℕ → Ω → ℝ) (G H : Ω → ℝ)
    (hG : ∀ᵐ ω ∂P,
      Tendsto (fun k => Gk k ω) atTop (𝓝 (G ω)))
    (hH : ∀ᵐ ω ∂P,
      Tendsto (fun k => Hk k ω) atTop (𝓝 (H ω)))
    (hSign : ∀ᵐ ω ∂P,
      ∀ k, Gk k ω + Hk k ω ≤ 0) :
    ∀ᵐ ω ∂P, G ω + H ω ≤ 0 := by
  filter_upwards [hG, hH, hSign] with ω hg hh hs
  have hsum : Tendsto (fun k => Gk k ω + Hk k ω)
      atTop (𝓝 (G ω + H ω)) := hg.add hh
  have hnonpos : ∀ᶠ k in atTop,
      Gk k ω + Hk k ω ∈ Set.Iic (0 : ℝ) :=
    Filter.Eventually.of_forall hs
  exact isClosed_Iic.mem_of_tendsto hsum hnonpos
