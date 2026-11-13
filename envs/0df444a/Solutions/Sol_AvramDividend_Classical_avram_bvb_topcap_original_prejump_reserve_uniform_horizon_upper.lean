-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_topcap_original_prejump_reserve_uniform_horizon_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T10:07:28.364368+00:00
-- url     : https://prove2.me/submissions/4cf03322-b917-4350-8655-9b304824fcc2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_original_global_postpayment_upper_horizon_strip
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T →
      Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s ω - rightLimit D s ω) t ≤
        max (x + max ((T : ℝ) * X.drift) 0) 0 := by
  let H : ℝ := max (x + max ((T : ℝ) * X.drift) 0) 0
  have hglobal :=
    AvramDividend.Classical.avram_bv_residual9_original_global_postpayment_upper_horizon_strip
      X hBV x D hD T
  filter_upwards [hglobal] with ω hω
  intro t ht
  let f : ℝ≥0 → ℝ := fun s => x + X.X s ω - rightLimit D s ω
  have hbounded : ∀ s : ℝ≥0, s ≤ t → f s ∈ Iic H := by
    intro s hs
    exact (hω s (hs.trans ht)).trans (le_max_left _ _)
  have hmem : ∀ᶠ s in 𝓝[≤] t, f s ∈ Iic H := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hbounded s hs
  have hz : f.leftLim t ≤ H :=
    isClosed_Iic.mem_of_mapClusterPt (mapClusterPt_leftLim f t) hmem
  exact hz
