-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_band_clock_le_ruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:16:30.746251+00:00
-- url     : https://prove2.me/submissions/c90f7f33-a90d-4041-b1f7-55279df8b011

import Mathlib
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (δ R : ℝ) (hδ : 0 < δ) (θ : Ω → ℝ≥0)
    (hprefix : ∀ ω t, t < θ ω →
      x + X.X t ω - rightLimit D t ω ∈ Icc δ R) :
    ∀ ω, (θ ω : ℝ≥0∞) ≤ ruinTime X x D ω := by 
  intro ω
  unfold ruinTime
  refine le_iInf (fun t => le_iInf (fun ht => ?_))
  have h : θ ω ≤ t := by
    by_contra hn
    have hb := (hprefix ω t (lt_of_not_ge hn)).1
    have hd := dividendStrategy_le_rightLimit D hD ω t
    change x + X.X t ω - D t ω < 0 at ht
    linarith
  exact_mod_cast h
